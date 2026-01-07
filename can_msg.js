/**************************************************************
 * GLOBAL
 * TODO:
 * Remove borders on "What is the CAN Bus?" textarea 
 * Get it working with known good messages
 *  Passing vs. failing info: DATA ordering; both hex and decimal values? Value of RAW CAN msg? Take out new lines?
 * Calculate CRC
 *  Too often it's the same value
 *  Is it being done correctly?  What about additional 0s added at end?
 * Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
 * Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
 * 
 * Test extended
 * Test heavy stream
 * Test negatives
 * Label fields for each parsed message
 * More user friendly explanation up front
 * 
 *
 * Split out user message creation to a separate file from consuming message stream? 
 * Endian-ness - do different fields have different endian-ness?
 * From https://en.wikipedia.org/wiki/Endianness :
 * Many IETF RFCs use the term network order, meaning the order of transmission for bytes over the wire in network protocols. 
 * Among others, the historic RFC 1700 defines the network order for protocols in the Internet protocol suite to be big-endian.
 * However, not all protocols use big-endian byte order as the network order. The Server Message Block (SMB) protocol uses 
 * little-endian byte order. In CANopen, multi-byte parameters are always sent least significant byte first (little-endian). 
 * The same is true for Ethernet Powerlink.
 * 
 * [DLC|DATA|CRC] - These fields *might* have the ability for [big|little] endian-ness
 * DLC - *NOT* multi-byte, *AND* it's important that there's no confusion WRT the value,
 * because it's a publicly visible value that should not be ambiguous.
 * Assume DLC is big-endian
 * 
 * DATA - Could be either [big|little] endian
 * 
 * CRC - *IS* multi-byte, *AND* it's important that there's no confusion WRT the value,
 * because it's a publicly visible value that should not be ambiguous.
 * Also, it seems like calculating the CRC would be easier to do bit by bit under big-endian network order
 * Assume CRC is big-endian
***************************************************************/

// Global variable definitions
var ID_FLD_LEN = 11;
var XID_FLD_LEN = 18;
var DLC_FLD_LEN = 4;
var CRC_FLD_LEN = 15;
var ACK_FLD_LEN = 2;
var EOF_FLD_LEN = 7;
var IFS_FLD_LEN = 3;

var STUFF_TRIGGER_CNT = 5;
var CRC_POLYNOMIAL = 0x4599;

var is_data_index_order_big_endian = true;
var is_data_in_bytes_big_endian = true;

/* ***************************************************************************
* Utility fxn to create a string from a number value with both hexa and 
* decimal number format, to make it easier to read for a wider audience
* *************************************************************************** */
function make_hex_and_decimal (number)  {
  return "0x" + (number >>> 0).toString(16) + " (" + number.toString(10) + ")";
}

/**************************************************************
 * Hold 2 numbers in 1 object
 * TODO: Does something like a pair() class already exist?
 * Seems like it should; feels like re-inventing the wheel here
***************************************************************/
class numPair {
  left;
  right;

  constructor (left, right) {
    this.left = left;
    this.right = right;
  }
}

/**************************************************************
 * Copied from 
 * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/random#examples
 * 
***************************************************************/
function getRandomIntInclusive(min, max) {
  const minCeiled = Math.ceil(min);
  const maxFloored = Math.floor(max);
  // The maximum is inclusive and the minimum is inclusive
  return Math.floor(Math.random() * (maxFloored - minCeiled + 1) + minCeiled); 
}

/**************************************************************
 * Hold information needed for bit-by-bit CRC calculation
***************************************************************/
class crcHolder {
  curr_reg_window;
  num_data_bits;
  polynomial;
  computed_crc;
  poly_bit_size;

  constructor (polynomial)  {
    this.curr_reg_window = 0;
    this.num_data_bits = 0;
    this.polynomial = polynomial;
    this.computed_crc = 0;
    this.poly_bit_size = 0;

    // Infer the polynomial's size by finding the maximum set bit
    var num_msb0_loops = 0;
    for (var mask32 = 0x80000000; mask32 > 0x0; mask32 >>>= 1) {
      if (mask32 & polynomial)
        break;
      else  {
        num_msb0_loops++;
      }
    }

    this.poly_bit_size = 32 - num_msb0_loops;
  }

  /**************************************************************
   * Account for the next bit from the frame in our ongoing CRC
   * calculation
  ***************************************************************/
  next_bit_crc_calc (next_bit) {

    this.curr_reg_window <<= 1;
    this.curr_reg_window |= (next_bit & 0x1);
    this.num_data_bits++;

    if (this.num_data_bits >= this.poly_bit_size) {
      // TODO: Do I have to wait until I've gathered 15 or 16 bits before starting the calculations?
      var is_xor_with_polyg = this.curr_reg_window ^ this.computed_crc;

      this.computed_crc <<= 1;

      if (is_xor_with_polyg)
        this.computed_crc ^= this.polynomial;

    }
  }

  /**************************************************************
   * Account for bit(s) from a given field
   * TODO: Is there a way to add a function with > 1 parameter to
   * a js class?
  ***************************************************************/
  add_bits_to_crc (num_pair) {

    var fld_data = num_pair.left;
    var num_bits_in_fld = num_pair.right;
    var mask = 0x1;

    if (num_bits_in_fld > 0)  {
      mask = 0x1 << (num_bits_in_fld - 1);
      for (; mask > 0; mask >>>= 1) {
        this.next_bit_crc_calc ((mask & fld_data) ? 1 : 0);
      }
    }
  }

  /**************************************************************
   * TODO: Using as Getter, but not preceding with [get]
   * FIX?
  ***************************************************************/
  get_computed_crc_final()  {
    var idx;
    var final_mask = 0x0;

    for (idx = 0; idx < this.poly_bit_size; idx++)  {
      // Pad with additional [0]{poly_bit_size} bits and returned computed CRC
      // TODO: Some specify doing this; others don't
      this.next_bit_crc_calc (0);
      final_mask <<= 0x1;
      final_mask |= 0x1;
    }

    // Make sure our final computed CRC is limited by polynomial size + 1
    this.computed_crc &= final_mask;
    // The CRC Delimiter is considered a separate field and doesn't get bit stuffed
    return this.computed_crc;
  }

  /**************************************************************
   * 
  ***************************************************************/
  get_poly_bit_size () {
    return this.poly_bit_size;
  }
}


/**************************************************************
 * Class to hold formatted CAN bus data field info with visual
 * spaces between nibbles|bytes and fields
 * Field names are shown below with alignment to the corresponding
 * data
***************************************************************/
class presentationStr {
  data_str;
  field_guide;

  reset() {
    this.data_str =    "";
    this.field_guide = "";
  }

  constructor() {
    this.reset();
  }
}

/**************************************************************
 * Hacky class object to allow for passing by reference
 * TODO: I'm sure there's a better way to do this
***************************************************************/
class passByRefNum  {
  val;

  constructor (num_val) {
    this.val = num_val;
  }
}

/* ***************************************************************************
 * BEGIN CAN BUS MESSAGE STREAM PARSING CODE
 * TODO: I tried separating the user friendly CAN bus message generation and 
 * the functionality that parses a CAN bus message stream, but I ran into import
 * problems.  I'll get the basics working and then separate these 2 things into
 * separate class files if I'm able.
 * *************************************************************************** */
// TODO: Should these be inside the class below? Should the class be renamed?
// CAN bus message handling states
var GET_SOF = 0;
var GET_MSG_ID = 1;
var GET_RTR = 2;
var GET_IDE = 3;
var GET_XID = 4;
var GET_R0 = 5;
var GET_R1 = 6;
var GET_DLC = 7;
var GET_DATA = 8;
var GET_CRC = 9;
var GET_CRC_DELIMITER = 10;
var GET_ACK = 11;
var GET_EOF = 12;
var GET_IFS = 13;
var MSG_HARD_FAIL = 14;
var MSG_ENDED = 15;

// Values for usr_msg_status
var SUCCESS = 0;
var INFLIGHT = 1;
var SOFT_ERROR = 2;
var FATAL_ERROR = 3;
var INTERNAL_FAIL = 4;

class canMsgParseState {
  can_msg_stream;
  curr_str_idx;
  curr_msg_number;

  usr_msg_raw;
  usr_msg_xy_stuffed;
  usr_msg_status;

  parsing_state;
  curr_hdr_bit_val;
  prev_hdr_bit_val;
  num_consecutive;
  num_stuffed;
  failure_msg;
  msg_id;
  num_msg_id_bits;
  extended_msg_id;
  absolute_msg_id;
  num_ext_msg_id_bits;
  is_rtr;
  is_extended;
  r0_val;
  r1_val;
  data_length_code;
  num_dlc_bits;
  data;
  num_data_bits_expected;
  num_data_bits_actual;
  senders_crc;
  calculated_crc;
  num_crc_bits;
  num_ack_bits;
  num_eof_bits;
  num_ifs_bits;
  post_hard_fail_seq_1s_cnt;
  is_stuffing_on;
  line_num;
  column;
  SOF_start_line;
  SOF_start_col;
  is_end_of_stream;
  parserCrc;

  reset_for_single_msg ()  {
    this.usr_msg_status = INFLIGHT;
    this.parsing_state = GET_SOF;
    this.SOF_start_line = 0;
    this.SOF_start_col = 0;
    
    // Bit position in the header; ignores bit stuffing;
    this.curr_hdr_bit_val = 0;
    this.prev_hdr_bit_val = 0;
    this.num_consecutive = [0,0];
    this.num_stuffed = [0,0];
    this.failure_msg = "";
    this.msg_id = 0;
    this.num_msg_id_bits = 0;
    this.extended_msg_id = 0;
    this.absolute_msg_id = 0;
    this.num_ext_msg_id_bits = 0;
    this.is_rtr = 0;
    this.is_extended = 0;
    this.r0_val = 0;
    this.r1_val = 0;
    this.data_length_code = 0;
    this.num_dlc_bits = 0;
    this.data = [0,0,0,0,0,0,0,0];
    this.senders_crc = 0;
    this.calculated_crc = 0;
    this.num_data_bits_expected = 0;
    this.num_data_bits_actual = 0;
    this.num_crc_bits = 0;
    this.num_ack_bits = 0;
    this.num_eof_bits = 0;
    this.num_ifs_bits = 0;
    this.post_hard_fail_seq_1s_cnt = 0;
    this.is_stuffing_on = true;
    this.usr_msg_raw = "";
    this.usr_msg_xy_stuffed = "";
    this.parserCrc = new crcHolder(CRC_POLYNOMIAL);
  
  }

  constructor (in_stream)  {
    this.can_msg_stream = in_stream;
    this.curr_str_idx = 0;
    this.curr_msg_number = 0;
    this.line_num = 1;
    this.column = 1;
    this.is_end_of_stream = false;
    this.reset_for_single_msg();
  }

  /* ***************************************************************************
  * Utility fxn to mark bit position of failure in the header
  * *************************************************************************** */
  mark_failure (error_msg, failure_severity)  {

    if (this.failure_msg.length > 0)
      this.failure_msg += "\n";
    
    this.failure_msg += error_msg + " (line " + this.line_num + ":" + this.column + "); parsing_state = " + this.parsing_state;

    if (failure_severity == FATAL_ERROR)  {
      this.usr_msg_status = failure_severity;
      this.parsing_state = MSG_HARD_FAIL;
      this.is_stuffing_on = false;
      this.post_hard_fail_seq_1s_cnt = 0;
    
    } else if (failure_severity == SOFT_ERROR) {
      // TODO: Need to mark where soft failure occurred for user
      this.usr_msg_status = failure_severity;

    } else  {
      this.usr_msg_status = INTERNAL_FAIL;
    }
  }

  /* ***************************************************************************
  * Utility fxn to print out the current message state
  * *************************************************************************** */
  can_msg_info_str ()  {
    var info_str = "";

    if (this.curr_msg_number > 1)
      info_str += "\n";

    info_str += "CAN Message #" + this.curr_msg_number;
    info_str += "\nSOF starts at line:column " + this.SOF_start_line + ":" + this.SOF_start_col;
    info_str += "\nCAN msg: Raw, XY stuffed";
    info_str += "\n" + this.usr_msg_raw;
    info_str += "\n" + this.usr_msg_xy_stuffed;
    info_str += "\n";

    if (this.usr_msg_status != SUCCESS) {
      info_str += "\nFailure message = " + this.failure_msg;
      info_str += "\ncurr_hdr_bit_val = " + this.curr_hdr_bit_val;
      info_str += "\nprev_hdr_bit_val = " + this.prev_hdr_bit_val;
      info_str += "\nconsecutive 0 count = " + this.num_consecutive[0];
      info_str += "\nconsecutive 1 count = " + this.num_consecutive[1];

    } else  {
      // Using parsed data we just consumed, create a user consumable representation of the CAN bus message to
      // use for a "disassembly" check
      var round_trip_msg_descr = new presentationStr();
      var round_trip_msg_data = new generatedCanMsg (this.absolute_msg_id, this.is_rtr, this.data_length_code, this.data);
      make_can_msg_str (round_trip_msg_data, round_trip_msg_descr);

      // Do a round trip check....do the collected and generated representations match?
      var generated_bit_str = round_trip_msg_descr.data_str.replaceAll(" ", ""); //.replaceAll("x", "0").replaceAll("y", "1");
      // generated_bit_str = generated_bit_str.replaceAll("X", "0").replaceAll("Y", "1");

      var collected_bit_str = this.usr_msg_xy_stuffed.replaceAll(" ", "");  //.replaceAll("x", "0").replaceAll("y", "1");
      // collected_bit_str = collected_bit_str.replaceAll("X", "0").replaceAll("Y", "1");

      if (generated_bit_str != collected_bit_str) {
        info_str += "\nINTERNAL FAILURE: Mismatch between collected CAN message and user friendly generated message!";
        info_str += "\nCollected: " + collected_bit_str;
        info_str += "\nGenerated: " + generated_bit_str;

      } else  {
        info_str += "\n" + round_trip_msg_descr.data_str;
        info_str += "\n" + round_trip_msg_descr.field_guide;
        info_str += "\n\n";
      }
    }

    info_str += "\nmsg_id = " + make_hex_and_decimal(this.msg_id);
    info_str += "\nextended_msg_id = " + make_hex_and_decimal (this.extended_msg_id);
    info_str += "\nabsolute_msg_id = " + make_hex_and_decimal (this.absolute_msg_id);
    info_str += "\nis_rtr = " + this.is_rtr + " (" + (this.is_rtr == 0 ? "false" : "true") + ")";
    info_str += "\nis_extended = " + this.is_extended + " (" + (this.is_extended == 0 ? "false" : "true") + ")";
    info_str += "\nr0_val = " + this.r0_val;
    info_str += "\nr1_val = " + this.r1_val;
    info_str += "\ndata_length_code = " + make_hex_and_decimal(this.data_length_code);
    info_str += "\ndata = ";

    for (var idx = this.data_length_code - 1; idx >= 0; idx--)  {
      // Display big-endian with most significant bytes 1st
      info_str += "[" + make_hex_and_decimal (this.data[idx]) + "] ";
    }

    info_str += "\nsenders_crc = " + make_hex_and_decimal (this.senders_crc);

    if (this.usr_msg_status != SUCCESS) {
      info_str += "\nnum_data_bits_expected = " + this.num_data_bits_expected;
      info_str += "\nnum_data_bits_actual = " + this.num_data_bits_actual;
      info_str += "\nnum_crc_bits = " + this.num_crc_bits;
      info_str += "\nnum_eof_bits = " + this.num_eof_bits;
      info_str += "\nnum_ifs_bits = " + this.num_ifs_bits;
      info_str += "\nis_stuffing_on = " + this.is_stuffing_on;
      info_str += "\nnum stuffed 0s = " + this.num_stuffed[0];
      info_str += "\nnum stuffed 1s = " + this.num_stuffed[1];
    }
    
    // Make a little space between messages
    info_str += "\n\n";

    return info_str;
   
  }

  /* ***************************************************************************
  * Handle the current non-stuffed bit based on what segment of the CAN message we're
  * currently dealing with.  The caller will filter out stuffed bits
  * *************************************************************************** */
  eat_non_stuffed_bit (curr_bit)  {

      // TODO: This isn't working
      // if (this.curr_msg_state < GET_CRC)
      //   this.crcMachine.add_bits_to_crc (new numPair (curr_bit, 1));
      this.usr_msg_xy_stuffed += curr_bit;

      if (this.parsing_state == GET_SOF)  {
        if (curr_bit == 0)  {
          this.SOF = 0;
          this.parsing_state = GET_MSG_ID;
          this.SOF_start_line = this.line_num;
          this.SOF_start_col = this.column;
          this.parserCrc.add_bits_to_crc (new numPair (this.SOF, 1));
        }

      } else if (this.parsing_state == GET_MSG_ID)  {
        this.msg_id <<= 1;
        this.msg_id |= this.curr_hdr_bit_val;
        this.num_msg_id_bits++;
        if (this.num_msg_id_bits == ID_FLD_LEN)  {
          this.parserCrc.add_bits_to_crc (new numPair (this.msg_id, ID_FLD_LEN));
          this.parsing_state = GET_RTR;
          this.absolute_msg_id = this.msg_id;
        }
      
      } else if (this.parsing_state == GET_RTR) {
        // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
        // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
        this.is_rtr = this.curr_hdr_bit_val;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* RTR */, 1));
        if (this.is_extended)
          this.parsing_state = GET_R1;
        else
          this.parsing_state = GET_IDE;

      } else if (this.parsing_state == GET_IDE) {
        this.is_extended = this.curr_hdr_bit_val;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* IDE */, 1));
        // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
        // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
        if (this.is_extended == 0)  
          // IDE bit is DOMINANT
          this.parsing_state = GET_R0;
        else 
          this.parsing_state = GET_XID;
        

      } else if (this.parsing_state == GET_XID) {
        this.extended_msg_id <<= 1;
        this.extended_msg_id |= this.curr_hdr_bit_val;
        this.num_ext_msg_id_bits++;

        // TODO:
        // this.num_ext_msg_id_bits++;
        // this.extended_msg_id |= (this.curr_hdr_bit_val << (XID_FLD_LEN - this.num_ext_msg_id_bits));

        if (this.num_ext_msg_id_bits == XID_FLD_LEN)  {
          this.parsing_state = GET_RTR;
          this.SRR = this.RTR;
          this.parserCrc.add_bits_to_crc (new numPair (this.extended_msg_id, XID_FLD_LEN));
          this.absolute_msg_id = (this.msg_id << XID_FLD_LEN) | this.extended_msg_id;
        }
      } else if (this.parsing_state == GET_R0)  {
        this.r0_val = this.curr_hdr_bit_val;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* RO */, 1));
        this.parsing_state = GET_DLC;

      } else if (this.parsing_state == GET_R1)  {
        this.r1_val = this.curr_hdr_bit_val;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* R1 */, 1));
        this.parsing_state = GET_R0;

      } else if (this.parsing_state == GET_DLC) {
        this.num_dlc_bits++;
        this.data_length_code |= (this.curr_hdr_bit_val << (DLC_FLD_LEN - this.num_dlc_bits));

        if (this.num_dlc_bits == DLC_FLD_LEN)  {
          // Done processing the Data Length Code field
          
          if (this.data_length_code > 0) {
            if (this.data_length_code > 8)  {
              // There are 4 bits, so 9-15 can be represented, but our ceiling is still 8
              this.data_length_code = 8;

              if (this.RTR) {
                // This is a Remote Transfer Request (READ).  There should be NO data
                this.mark_failure ("Expect DLC value of 0 for all RTR frames", SOFT_ERROR);
              }
            }

            // TODO: Assuming the bits that represent [9-15] will be added to the CRC calculation "as is"
            this.parserCrc.add_bits_to_crc (new numPair (this.data_length_code, DLC_FLD_LEN));
            this.parsing_state = GET_DATA;
            this.num_data_bits_expected = this.data_length_code * 8;
            
          } else {
            this.parsing_state = GET_CRC;
          }
        }

      } else if (this.parsing_state == GET_DATA)  {
          var data_idx = Math.floor(this.num_data_bits_actual/8);
          var chunk = this.data[data_idx];
          chunk <<= 1;
          chunk |= this.curr_hdr_bit_val;
          this.data[data_idx] = chunk;
          this.parserCrc.add_bits_to_crc (new numPair (this.data[data_idx], 8));
          this.num_data_bits_actual += 1;

          if (this.num_data_bits_actual == this.num_data_bits_expected)
              this.parsing_state = GET_CRC;

      } else if (this.parsing_state == GET_CRC) {
        this.num_crc_bits += 1;
        if (this.num_crc_bits == 1)
          // TODO: Questions remain on how this is calculated
          // TODO: In case of actual bit-banging, is there a SMRT way to do
          // this calculation asynchronously? Does it even matter?
          this.calculated_crc = this.parserCrc.get_computed_crc_final();

        this.senders_crc <<= 0x1;
        // Add bits in INCLUDING ending delimiter
        this.senders_crc |= this.curr_hdr_bit_val;

        if (this.num_crc_bits == (CRC_FLD_LEN))  {
          // The CRC Delimiter is up next and bit stuffing is turned off
          this.is_stuffing_on = false;
          this.parsing_state = GET_CRC_DELIMITER;
        }

      } else if (this.parsing_state == GET_CRC_DELIMITER) {
          if (this.curr_hdr_bit_val != 1) {
            this.mark_failure("Expected CRC delimiter to be RECESSIVE (1)!", SOFT_ERROR);
          } else  {
            this.parsing_state = GET_ACK;
            if (this.senders_crc != this.calculated_crc)
              this.mark_failure ("Calculated CRC does NOT match sender's CRC! (" + make_hex_and_decimal (this.calculated_crc) + " <> " + make_hex_and_decimal (this.senders_crc) + ")", SOFT_ERROR);
          }

      } else if (this.parsing_state == GET_ACK) {
        this.num_ack_bits += 1;
        if (this.num_ack_bits == 1 && this.curr_hdr_bit_val != 1) {
          // In a bit-banging solution, now would be the time to drive ACKl to
          // ground in the case of a CRC or other error that wasn't fatal
          this.mark_failure("ACK must be RECESSIVE (1)!", SOFT_ERROR);

        } else if (this.num_ack_bits == ACK_FLD_LEN)  {
          if (this.curr_hdr_bit_val != 1)  
            this.mark_failure("ACK delimiter must be RECESSIVE (1)!", SOFT_ERROR);

          this.parsing_state = GET_EOF;
        }
      } else if (this.parsing_state == GET_EOF) {
          if (this.curr_hdr_bit_val == 0)
            this.mark_failure ("Expected recessive (1) EOF bit [" + (EOF_FLD_LEN - this.num_eof_bits) + "] but got DOMINANT (0)", FATAL_ERROR);
          
          this.num_eof_bits += 1;
          
          if (this.num_eof_bits == EOF_FLD_LEN)
              this.parsing_state = GET_IFS;

      } else if (this.parsing_state == GET_IFS) {
          if (this.curr_hdr_bit_val == 0)
            this.mark_failure ("Expected recessive (1) IFS bit [" + (EOF_FLD_LEN - this.num_eof_bits) + "] but got DOMINANT (0)", FATAL_ERROR);
          
          this.num_ifs_bits += 1;
          
          if (this.num_ifs_bits == IFS_FLD_LEN) {
            this.parsing_state = MSG_ENDED;
            if (this.usr_msg_status == INFLIGHT)
              this.usr_msg_status = SUCCESS;
          }

      } else if (this.parsing_state == MSG_HARD_FAIL) {
        // Encountered a HARD FAIL; this message has failed
        // A bit-banging solution would ask for a retry somehow
        if (this.curr_hdr_bit_val == 0)
          this.post_hard_fail_seq_1s_cnt = 0;
        else
          this.post_hard_fail_seq_1s_cnt += 1;

        if (this.post_hard_fail_seq_1s_cnt >= (EOF_FLD_LEN + IFS_FLD_LEN)) {
          this.parsing_state = MSG_ENDED;
        }
        
      } else {
        this.mark_failure("Fell all the way through to No Man's Land!", INTERNAL_FAIL);
      }
    }

  /* ***************************************************************************
  * Determine if the current bit is a stuff bit or not
  /* ************************************************************************* */
  is_stuff_bit (curr_bit_val) {
    var is_stuffed = false;
    var other_idx;
    
    if (this.is_stuffing_on) {
      // Prepare for book keeping
      if (curr_bit_val == 1)
        other_idx = 0;
      else
        other_idx = 1;

      if (this.parsing_state < MSG_HARD_FAIL && this.parsing_state < MSG_ENDED) {
        if (this.parsing_state == GET_SOF)  {
          // Account for the very 1st SOF bit, which should be DOMINANT (0)
          this.num_consecutive[0] = 1;
          this.num_consecutive[1] = 0;

        } else  {
          if (curr_bit_val != this.prev_hdr_bit_val) {
            if (this.num_consecutive[other_idx] == STUFF_TRIGGER_CNT)  {
              // This is a stuffed bit; let the caller know to toss it!
              is_stuffed = true;
              this.num_stuffed[curr_bit_val] += 1;

              if (curr_bit_val == 0)  {
                this.usr_msg_xy_stuffed += "x";

              } else if (curr_bit_val == 1) {
                this.usr_msg_xy_stuffed += "y";
              
              }  else {
                this.usr_msg_xy_stuffed += "Z";
              }

              this.num_consecutive[other_idx] = 0;
              this.num_consecutive[curr_bit_val] = 1;
            
            } else if (this.num_consecutive[other_idx] < STUFF_TRIGGER_CNT) {
              // Polarity has flipped; reset our counters
              this.num_consecutive[other_idx] = 0;
              this.num_consecutive[curr_bit_val] = 1;
            
            } else  {
              this.mark_failure("Too many sequential " + other_idx + "s!", FATAL_ERROR);

            }

          } else if (curr_bit_val == this.prev_hdr_bit_val)  {
            if (this.num_consecutive[curr_bit_val] == (STUFF_TRIGGER_CNT + 1))
                this.mark_failure("Expected a bit stuffed " + other_idx, FATAL_ERROR);
            else
                this.num_consecutive[curr_bit_val] += 1;
          }
        } 
      }
    }
    
    return is_stuffed;

  }
  /* ***************************************************************************
  * Handle the next valid bit from the CAN message.
  * NOTE Writing code with the intent of possibly turning this into C|C++ code 
  * if/when I decide to do some bit-banging over GPIOs
  * *************************************************************************** */
  handle_nxt_msg_bit (bit_val)  {

    this.curr_hdr_bit_val = bit_val;

    if (!this.is_stuff_bit (bit_val)) {
      this.eat_non_stuffed_bit (bit_val);
    }

    // Save off curr->prev for bit stuffing checks
    this.prev_hdr_bit_val = this.curr_hdr_bit_val;

  }

  /* ***************************************************************************
  * Parse the next CAN bus message out of the current stream
  * *************************************************************************** */
  get_next_can_msg () {
    var msg_descr = "";
    this.reset_for_single_msg();
    this.curr_msg_number++;

    this.usr_msg_xy_stuffed = "";
    this.usr_msg_raw = "";
    var next_char;

    while (this.parsing_state != MSG_ENDED && this.usr_msg_status != INTERNAL_FAIL && !this.is_end_of_stream) {
      next_char = this.can_msg_stream[this.curr_str_idx];

      if (next_char == '\r' || next_char == '\n')  {
        // Carriage return or line feed (CR or LF)
        if (this.usr_msg_raw.length > 0)
          // Don't start adding until the actual message's SOF
          this.usr_msg_raw += next_char;
        if (this.curr_str_idx + 1 < this.can_msg_stream.length) {
          if ((next_char == '\r' && this.can_msg_stream[this.curr_str_idx + 1] == '\n')
            || (next_char == '\n' && this.can_msg_stream[this.curr_str_idx + 1] == '\r'))  {
            // CRLF or LFCR indicates newline
            this.curr_str_idx++;
            if (this.usr_msg_raw.length > 0)
              // Don't start adding until the actual message's SOF
              this.usr_msg_raw += next_char;

          }

          this.line_num += 1;
          this.column = 1;
        }

      } else if (next_char == '0' || next_char == 'x' || next_char == 'X' 
        || next_char == '1' || next_char == 'y' || next_char == 'Y')  {
        // It's a legit character [xX] -> 0 stuff bit; [yY] -> 1 stuff bit
        this.usr_msg_raw += next_char;

        if (next_char == 'x' || next_char == 'X')
          next_char = 0;
        else if (next_char == 'y' || next_char == 'Y')
          next_char = 1;

        this.handle_nxt_msg_bit (next_char);
        this.column++;
      
      } else if ((next_char == '\s' || next_char == '\t'))  {
        if (this.usr_msg_raw.length > 0)
          // Don't start adding until the actual message's SOF
          this.usr_msg_raw += next_char;
        this.column++;

      } else  {
        this.column++;

      }

      // Marching ever forward towards completion
      this.curr_str_idx++;

      if (this.curr_str_idx == this.can_msg_stream.length)  {
        this.is_end_of_stream = true;
        if ((this.usr_msg_status == INFLIGHT && this.parsing_state > GET_SOF) || this.usr_msg_status == SOFT_ERROR) {
          this.mark_failure ("Character stream ended before message was complete", FATAL_ERROR);
        }
      }
    }

    if (this.SOF_start_line > 0 || this.parsing_state == MSG_ENDED || this.parsing_state == MSG_HARD_FAIL)
      // Only print out when there's an actual message. 
      msg_descr = this.can_msg_info_str();
  
    return msg_descr;
  }
}


/* ***************************************************************************
 * BEGIN USER GENERATED CAN BUS MESSAGE CODE
 * TODO: I tried separating the user friendly CAN bus message generation and 
 * the functionality that parses a CAN bus message stream, but I ran into import
 * problems.  I'll get the basics working and then separate these 2 things into
 * separate class files if I'm able.
 * *************************************************************************** */
var EXT_MSG_MASK_U11 = 0x1FFC0000;   // 0b1 1111 1111 1100 0000 0000 0000 0000; 
var EXT_MSG_MASK_L18 = 0x3FFFF;      // 0b0 0000 0000 0011 1111 1111 1111 1111;

/**************************************************************
 * Holds data for CAN 2.0[A|B] message fields
***************************************************************/
class generatedCanMsg  {
  SOF;
  MSG_ID;
  RTR;
  SRR;
  IDE;
  EXT_MSG_ID;
  r1;
  r0;
  DLC;
  DATA;
  CRC;
  CRC_D;
  ACK;
  EOF;
  IFS;

  generatorCrc;

  constructor (in_msg_id, in_rtr, in_dlc, in_data) {
    this.zero_all_fields();
    this.generatorCrc = new crcHolder(CRC_POLYNOMIAL);
    // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
    // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
    
    // Start Of Frame is always DOMINANT (0)
    this.SOF = 0;
    this.generatorCrc.add_bits_to_crc (new numPair (this.SOF, 1));

    var max_11bit_id = Math.pow (2, ID_FLD_LEN) - 1;
    
    if (in_msg_id <= max_11bit_id) {
      // 0 (DOMINANT) indicates 11-bit message ID
      this.IDE = 0;
      // Message ID *MUST* be in big-endian, network order for address conflict resolution to work
      this.MSG_ID = in_msg_id;
      this.EXT_MSG_ID = 0;

    } else  {
      // 1 (recessive) indicates extended format 29-bit message ID
      this.IDE = 1; 
      // mmmmmmmmmmmxxxxxxxxxxxxxxxxxx
      this.MSG_ID = (in_msg_id & EXT_MSG_MASK_U11) >>> XID_FLD_LEN;
      this.EXT_MSG_ID = (in_msg_id & EXT_MSG_MASK_L18);

    }

    this.generatorCrc.add_bits_to_crc (new numPair (this.MSG_ID, ID_FLD_LEN));

    
    this.RTR = ((in_rtr == 0) ? 0 : 1);
    // SRR is *always* recessive (1) 
    this.SRR = 1;

    // Reserved bits which must be set dominant (0), but accepted as either dominant or recessive 
    this.r0 = 0;
    this.r1 = 0;

    // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
    // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]

    if (this.IDE == 0)  {
      // Standard: [SOF|ID|-> RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
      this.generatorCrc.add_bits_to_crc (new numPair (this.RTR, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.IDE, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.r0, 1));

    } else  {
      // Extended: [SOF|ID|->SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
      this.generatorCrc.add_bits_to_crc (new numPair (this.SRR, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.IDE, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.EXT_MSG_ID, XID_FLD_LEN));
      this.generatorCrc.add_bits_to_crc (new numPair (this.RTR, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.r1, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.r0, 1));
    }

    if (this.RTR == 1)  {
      // NO DATA for a Remote Transmission Request (RTR)
      this.DLC = 0;

    } else {
      // TODO: DLC is a 4-bit field. So is it [big|little]-endian?
      this.DLC = in_dlc;

    }

    this.generatorCrc.add_bits_to_crc (new numPair (this.DLC, DLC_FLD_LEN));

    if (this.DLC > 0) {
      this.DATA = new Uint8Array(in_dlc);

      for (var idx = 0; idx < in_dlc; idx++) {
        this.DATA[idx] = in_data[idx];
        // TODO: Endian-ness of DATA?
        this.generatorCrc.add_bits_to_crc (new numPair (in_data[idx], 8));
      }
    }

    // TODO: Questions remain on how this is calculated
    this.CRC = this.generatorCrc.get_computed_crc_final();

    // CRC delimiter is required to be a recessive (1)
    this.CRC_D = 1;

    // Transmitter sends recessive (1) and any receiver can assert a dominant (0)
    // Followed by ACK delimiter (recessive)
    this.ACK = 0b11;

    // Must be recessive (1) 
    this.EOF = 0b1111111;

    // Must be recessive (1) 
    this.IFS = 0b111;
  }

  zero_all_fields ()  {
    this.SOF = 0;
    this.MSG_ID = 0;
    this.RTR = 0;
    this.SRR = 0;
    this.IDE = 0;
    this.EXT_MSG_ID = 0;
    this.r1 = 0;
    this.r0 = 0;
    this.DLC = 0;
    this.DATA = 0;
    this.CRC = 0;
    this.ACK = 0;
    this.EOF = 0;
    this.IFS = 0;
  }
}

/**************************************************************
 * Modifies the passed in field if stuff bits are needed
***************************************************************/
function bit_stuff_string (fld_data, prev_bit, seq_bit_cnt, total_stuff_cnt)  {
  var stuffed_str = "";

  // TODO:  00011111x00000y00010101100011001100010010111101111001110011111100001101110111111111111111
  //                ------ 6
  // Failure message = Too many sequential 0s! (line 1:15)
  // The y is stuff too late; it should be stuffed BEFORE the current character is added!

  for (var idx = 0; idx < fld_data.length; idx++) {
    var curr_char = fld_data[idx];
    stuffed_str += curr_char;

    var curr_bit = 0;
    if (curr_char == "0" || curr_char == "1")
      curr_bit = curr_char;
    else if (curr_char == "x" || curr_char == "X")
      curr_bit = 0;
    else if (curr_char == "y" || curr_char == "Y")
      curr_bit = 1;
    else
      // Probably a space or other non-data character
      curr_bit = 2;

    if (curr_bit == 0 || curr_bit == 1)  {
      var other_bit = (curr_bit == 0) ? 1 : 0;
      
      if (prev_bit.val == curr_bit) {
        seq_bit_cnt[curr_bit] += 1;

        if (seq_bit_cnt[curr_bit] == STUFF_TRIGGER_CNT) {
          // Stuffed 0 -> x; stuffed 1 -> y
          stuffed_str += (other_bit == 0) ? "x" : "y"
          total_stuff_cnt[other_bit] += 1;
          seq_bit_cnt[curr_bit] = 0;
          seq_bit_cnt[other_bit] = 1;
          // Only update this when curr_bit is [0|1]
          prev_bit.val = other_bit;
  
        } else  {
          // Only update this when curr_bit is [0|1]
          prev_bit.val = curr_bit;
        }

      } else  {
        // The bit has flipped!
        seq_bit_cnt[other_bit] = 0;
        seq_bit_cnt[curr_bit] = 1;
        // Only update this when curr_bit is [0|1]
        prev_bit.val = curr_bit;
      }
    }
  }

  return stuffed_str;

}

/**************************************************************
 * Move R2L through bit_string and insert a space every [x] bits
 * for readability
***************************************************************/
function make_readable_bit_string (number, bits_per_chunk, bit_len)  {
  readable_str = "";
  var num_bits_in_chunk = 0;
  var num_bits_done = 0;
  var past_limit = Math.pow (2, bit_len);

  for (var mask = 0x1; mask < past_limit; mask <<= 1) {
    if (number & mask)
      readable_str = "1" + readable_str;
    else
      readable_str = "0" + readable_str;

    num_bits_in_chunk++;
    num_bits_done++;
    if (bits_per_chunk > 0 && num_bits_in_chunk == bits_per_chunk && num_bits_done < bit_len) {
      readable_str = " " + readable_str;
      num_bits_in_chunk = 0;
    }
  }

  return readable_str;

}

/**************************************************************
 * Keeps the 2 strings in this class aligned for readability
***************************************************************/
function append_presentation_strings (descr, field_name, field_value) {

  // 0 000 0100 1010 0 0 0  0010  0000 0000 0101 0101  11  1111111  111 
  // SOF ID RTR IDE r0 DLC CRC ACK EOF IFS 

  descr.field_guide += field_name + " ";
  descr.data_str += field_value + " ";

  // Make sure we're aligned AFTER
  var tmp_str = "";
  if (descr.field_guide.length > descr.data_str.length)
    descr.data_str += tmp_str.padEnd(descr.field_guide.length - descr.data_str.length, " ");
  
  else if (descr.data_str.length > descr.field_guide.length)
    descr.field_guide += tmp_str.padEnd (descr.data_str.length - descr.field_guide.length, " ");
}

/**************************************************************
 * Generates CAN message from user's data. Includes bit stuffing
***************************************************************/
function make_can_msg_str (can_msg_data, msg_descr) {
  const seq_bit_cnt = new Array (0,0);
  const total_stuff_cnt = new Array (0,0);

  // SOF
  seq_bit_cnt[0] += 1;
  prev_bit = new passByRefNum(0);
  append_presentation_strings (msg_descr, "SOF", "0");

  // MSG_ID
  var tmp_str = "";
  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.MSG_ID, ID_FLD_LEN, ID_FLD_LEN), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "ID", tmp_str);

  if (can_msg_data.IDE == 1)  {
    // Extended frame - SRR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.SRR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "SRR", tmp_str);

  } else  {
    //   RTR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.RTR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "RTR", tmp_str);
  }
  
  // IDE
  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.IDE, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "IDE", tmp_str);
  
  if (can_msg_data.IDE == 1)  {
    // Extended frame
    //   extended ID
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.EXT_MSG_ID, 4, XID_FLD_LEN), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "EXT_ID", tmp_str);
    //   RTR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.RTR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "RTR", tmp_str);
    //   r1
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.r1, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "r1", tmp_str);
  }

  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.r0, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "r0", tmp_str);

  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.DLC, 4, DLC_FLD_LEN), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "DLC", tmp_str, DLC_FLD_LEN);

  for (var data_idx = 0; data_idx < can_msg_data.DLC; data_idx++) {
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.DATA[data_idx], 8, 8), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, data_idx == 0 ? "DATA" : "", tmp_str);
  }

  // Bit stuffing OFF
  // TODO: CRC - TODO: Add byte|nibble blanks
  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.CRC, 4, 15), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "CRC", tmp_str);

  append_presentation_strings (msg_descr, "CRC_D", can_msg_data.CRC_D);
  
  append_presentation_strings (msg_descr, "ACK", make_readable_bit_string (can_msg_data.ACK, 2, 2));
  append_presentation_strings (msg_descr, "EOF", make_readable_bit_string (can_msg_data.EOF, 7, 7));
  append_presentation_strings (msg_descr, "IFS", make_readable_bit_string (can_msg_data.IFS, 3, 3));

}

/**************************************************************
 * Utility fxn that returns an error description if a number is
 * out of an inclusive range
***************************************************************/
function num_in_range (field_name, num_str, min, max, callers_num) {
  var err_msg = "";
  callers_num.val = 0;
  var num_val = Number(num_str);

  if (isNaN(num_val)) {
    err_msg = num_str + " is not a valid decimal or hexadecimal (0x) number";
  
  } else if (num_val < min) {
    err_msg = num_str + " is less than minimum of " + min;
  
  } else if (num_val > max) {
    err_msg = num_str + " is greater than maximum of " + max;

  }

  if (err_msg != "")  {
    if (field_name != "") {
      err_msg = field_name + ": " + err_msg;
    }
    err_msg += "\n";
  } else  {
    // Return the value to our caller
    callers_num.val = num_val;
  }

    return err_msg;
}

/**************************************************************
 * Return an error description if there's anything wrong with
 * the CAN message ID the user entered.
***************************************************************/
function get_err_for_can_msg_field (msg_id_val)  {
  var err_msg = "";
  var users_msg_id = document.getElementById("msg_id_txt_box").value;

  if (users_msg_id.replaceAll (" ", "") == "")
    err_msg = "Please put a numeric value in the Message ID field.";
  else
    err_msg =  num_in_range ("Message ID", users_msg_id, 0, 0x1FFFFFFF, msg_id_val);

  return err_msg;
}

/**************************************************************
 * Return an error description if there's anything wrong with
 * the bytes the user entered into the data entries.  
***************************************************************/
function get_err_for_data_field (data_length_code, data_array)  {
  var accum_err_msg = "";

  var is_rtr = document.getElementById("is_rtr_chk_box");
  if (is_rtr != null) {
    if (is_rtr.checked)  {
      // This CAN msg is a Remote Transmission Request (RTR)
      data_length_code.val = 0;

    } else  {
      for (var idx = 0; idx < 8; idx++) {
        var data_fld = document.getElementById("data" + idx + "_txt_box");
        var err_msg = "";
        if (data_fld != null) {
          data_fld_num = new passByRefNum (0);
          err_msg = num_in_range ("Data[" + idx + "]", data_fld.value, 0, 0xFF, data_fld_num);
          if (err_msg == "")  { 
            data_array[idx] = data_fld_num.val;
            if (data_fld_num.val > 0)
              data_length_code.val = idx + 1;
          }

        } else  {
          err_msg = "Could not find Data[" + idx + "] (Developer issue)!\n";
        }
        accum_err_msg += err_msg;
      }
    }
  }

  return accum_err_msg;

}

/**************************************************************
 * Generate a glossary of the CAN bus messge fields for the user 
 * and discern which field names are appropriate for either
 * standard or extended messages
***************************************************************/
function make_field_glossary (is_extended)  {
  var glossary_descr = "GLOSSARY";

  // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
  // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]

  glossary_descr += "\nSOF:    Start Of Frame. A DOMINANT logical 0 is driven on an idle bus. Rest of frame follows.";
  glossary_descr += "\nID:     11-bit message ID. Lower IDs have higher priorities.";

  var rtr_desc = "\nRTR:    Remote Transmission Request. DOMINANT (0) for data frame; recessive (1) for remote request.";
  if (!is_extended)
    glossary_descr += rtr_desc;
  else
    glossary_descr += "\nSRR:    Must be recessive (1) for extended messages.";

  glossary_descr += "\nIDE:    DOMINANT (0) for 11-bit ID message identifiers; recessive (1) for extended 29-bit message identifiers.";

  if (is_extended)  {
    glossary_descr += "\nEXT_ID: Additional 18 bits for rest of 29-bit extended message identifier.";
    glossary_descr += rtr_desc;
    glossary_descr += "\nr1:     RESERVED";
  }

  glossary_descr += "\nr0:     RESERVED";
  glossary_descr += "\nDLC:    Data Length Code indicates length of DATA field ([0-8] bytes).";
  glossary_descr += "\nDATA:   [0-8] bytes of data.  Remote requests send no data, but their response probably will.";
  glossary_descr += "\nCRC:    15-bit Cyclic Redundancy Check for detecting transmission errors.";
  glossary_descr += "\nCRC_D:  1-bit CRC delimiter; must be a recessive (1). Bit stuffing is now OFF for remainder of message.";
  glossary_descr += "\nACK:    Acknowledgment; receiver indicates error detection via DOMINANT (0) on 1st of 2 ACK bits.";
  glossary_descr += "\nEOF:    End Of Frame; 7 recessive (1) bits in a row.";
  glossary_descr += "\nIFS:    Inter Frame Space; 3 recessive (1) bits in a row.";

  glossary_descr += "\n\nStuff bits are used to maintain synchronization since there is no clock signal on the CAN bus.";
  glossary_descr += "\nA bit of opposite polarity is inserted after five consecutive bits of the same polarity."
  glossary_descr += "\nIf a transmitter sends 5 [0]s in a row, it must send a [1] stuff bit (de-stuffed by receiver).";
  glossary_descr += "\nIf a transmitter sends 5 [1]s in a row, it must send a [0] stuff bit (de-stuffed by receiver).";
  glossary_descr += "\nBit stuffing is active from SOF to 15-bit calculated CRC and off from the CRC_D delimiter onwards.";


  return glossary_descr;
}

/**************************************************************
 * BEGIN EVENT HANDLER FUNCTIONS 
***************************************************************/
/**************************************************************
 * Validate user's input into fields for generating a CAN bus
 * message.
***************************************************************/
function gen_can_msg_btn_pressed (event) {
  var accum_err_msg = "";

  var gen_can_msg_pre = document.getElementById("gen_can_msg_pre");
  if (gen_can_msg_pre != null)  {
    gen_can_msg_pre.innerText = "";
  }

  var glossary_pre = document.getElementById ("glossary_pre");
  if (glossary_pre != null) {
    glossary_pre.innerText = "";
  }

  calculated_dlc = new passByRefNum (0);
  msg_id = new passByRefNum (0);
  accum_err_msg += get_err_for_can_msg_field(msg_id);
  data_array = new Uint8Array(8);
  accum_err_msg += get_err_for_data_field(calculated_dlc, data_array);

  if (accum_err_msg != "")  {
    alert (accum_err_msg);
  
  } else  {
    msg_descr = new presentationStr();
    can_msg_data = new generatedCanMsg (msg_id.val, get_rtr_checked(), calculated_dlc.val, data_array)
    make_can_msg_str (can_msg_data, msg_descr);

    if (gen_can_msg_pre != null)  {
      gen_can_msg_pre.innerText = msg_descr.data_str + "\n" + msg_descr.field_guide + "\n\n";

      gen_can_msg_pre.innerText += "Raw [x|y] stuff bits: ";
      var compressed_can_xy = msg_descr.data_str.replaceAll (" ", "");
      gen_can_msg_pre.innerText += compressed_can_xy;
      gen_can_msg_pre.innerText += "\n";

      gen_can_msg_pre.innerText += "Raw [0|1] stuff bits: ";
      var compressed_can_01 = compressed_can_xy.replaceAll ("x", "0");
      compressed_can_01 = compressed_can_01.replaceAll ("y", "1");
      gen_can_msg_pre.innerText += compressed_can_01 +"\n\n";

      if (glossary_pre != null)
        glossary_pre.innerText += make_field_glossary (can_msg_data.IDE == 1)
    }
  }
}

/**************************************************************
 * Zero out ALL 8 bytes of the Data field (user convenience)
***************************************************************/
function zero_data_bytes (event) {

  for (var idx = 0; idx < 8; idx++) {
    var data_fld = document.getElementById("data" + idx + "_txt_box");
    if (data_fld != null) {
      data_fld.value = "0x0";
    }
  }
}


/**************************************************************
 * Determine RTR [True|False]
***************************************************************/
function get_rtr_checked () {
  var is_rtr = false;

  var rtr_chk_box = document.getElementById("is_rtr_chk_box");
  if (rtr_chk_box != null) {
    if (rtr_chk_box.checked) {
      is_rtr = true;
    }
  }

  return is_rtr;
}

/**************************************************************
 * Handle RTR (Remote Transfer Request) checkbox event
***************************************************************/
function on_click_rtr_checkbox (event) {

  var is_rtr = get_rtr_checked ();
  for (var idx = 0; idx < 8; idx++) {
    var data_fld = document.getElementById("data" + idx + "_txt_box");
    if (data_fld != null) {
      if (is_rtr) {
        // Data bytes are invalid on an RTR, which is a request for data
        // from another node
        data_fld.readonly = true;
        data_fld.disabled = true;
      
      } else  {
        data_fld.readonly = false;
        data_fld.disabled = false;

      }
    }
  }
}

/**************************************************************
 * Decode the stream of CAN bus messages the user put into the
 * text box.
***************************************************************/
function on_click_decode (event) {
  var msg_stream_txt_box = document.getElementById ("can_msg_stream_txt_box");
  var decode_output_txtbox = document.getElementById ("decoded_stream_txt_box");

  if (msg_stream_txt_box == null) {
    alert ("DEVELOPER ERROR: can_msg_stream_txt_box MIA!");

  } else if (decode_output_txtbox == null)  {
    alert ("DEVELOPER ERROR: decoded_stream_txt_box MIA!");

  } else  {
    decode_output_txtbox.value = "";
    var msg_stream = msg_stream_txt_box.value;

    if (msg_stream.trim() == "")  {
      alert ("Text box is empty. Please fill with 1 or more CAN bus messages.");

    } else  {
      can_msg_stream_parser = new canMsgParseState (msg_stream);

      var is_msgs_done = false;
      var nxt_msg_summary;

      while (!can_msg_stream_parser.is_end_of_stream && !is_msgs_done) {
        nxt_msg_summary = can_msg_stream_parser.get_next_can_msg ();

        if (nxt_msg_summary == null || nxt_msg_summary == "")
          is_msgs_done = true;
        else  {
          decode_output_txtbox.value += nxt_msg_summary;
        }
      }
    }
  }
}

/**************************************************************
 * Generate a stream of randomized CAN bus messages for testing
***************************************************************/
function on_click_test_stream (event) {

  var msg_stream_txt_box = document.getElementById ("can_msg_stream_txt_box");

  if (msg_stream_txt_box == null) {
    alert ("DEVELOPER ERROR: can_msg_stream_txt_box MIA!");
  
  } else  {
    // Clear whatever is currently in the msg stream text box
    msg_stream_txt_box.value = "";
    var coin_toss;
    var idx;
    var can_msg_id;
    var is_rtr;
    var data_length_code;
    data_array = new Uint8Array(8);
    var msg_descr = new presentationStr();
    for (idx = 0; idx < 10; idx++)  {
      coin_toss = getRandomIntInclusive (0, 1);

      if (coin_toss == 0)
        // Standard frame
        can_msg_id = getRandomIntInclusive (0, 2047);
      else
        // Extended frame
        can_msg_id = getRandomIntInclusive (2048, 536870911);

      if (4 == getRandomIntInclusive (1,4)) {
        // 1 in 4 chance of RTR msg
        is_rtr = 1;
        data_length_code = 0;
      } else  {
        // NOT an RTR; let's randomly choose a DLC
        is_rtr = 0;
        data_length_code = getRandomIntInclusive (1,8);
      }

      if (is_rtr == 0 && data_length_code > 0)  {
        // data_array will be used this time
        var adx;
        for (adx = 0; adx < data_length_code; adx++)  {
          // Fill in the chosen array elements
          data_array[adx] = getRandomIntInclusive (0, 255);

        }

        var retry_cnt = 0;
        var last_idx = data_length_code - 1;
        while (data_array[last_idx] == 0 && retry_cnt < 5)  {
          // Most significant data byte should *NOT* be zero; otherwise, DLC should be smaller
          data_array[last_idx] = getRandomIntInclusive(1,255)
          retry_cnt++;
        }

        for (adx = data_length_code; adx < 8; adx++)
          // Zero out the elements that aren't active
          data_array[adx] = 0;
      }

      msg_descr.reset();
      can_msg_data = new generatedCanMsg (can_msg_id, is_rtr, data_length_code, data_array)
      make_can_msg_str (can_msg_data, msg_descr);

      msg_stream_txt_box.value += msg_descr.data_str.replaceAll (" ", "");
      msg_stream_txt_box.value += "\n";
      
      // msg_stream_txt_box.value += msg_descr.data_str;
      // msg_stream_txt_box.value += "\n";
      // msg_stream_txt_box.value += msg_descr.field_guide;
      // msg_stream_txt_box.value += "\nRand msg_id = 0x" + can_msg_id.toString(16) + "; is_rtr = " + is_rtr + "; DLC = " + data_length_code.toString(10) + ";";
      // msg_stream_txt_box.value += "\n\n";
    }
  }
}
/**************************************************************
 * <END> EVENT HANDLER FUNCTIONS 
***************************************************************/

/**************************************************************
 * BEGIN REGISTER EVENT HANDLERS
***************************************************************/
var gen_msg_btn = document.getElementById("gen_can_msg_btn");
if (gen_msg_btn != null)  {
  // When registering an event -> handler, must specify it as a function.  Seems like
  // this would be assumed, but I guess not!
  gen_msg_btn.addEventListener("click", function () { gen_can_msg_btn_pressed()} );

} else  {
  alert ("DEVELOPER ERROR: gen_can_msg_btn MIA!");
}

var clear_data_btn = document.getElementById ("clear_data_btn");
if (clear_data_btn != null) {
  clear_data_btn.addEventListener("click", function() {zero_data_bytes()});

} else  {
  alert ("DEVELOPER ERROR: clear_data_btn MIA!");
}

var is_rtr = document.getElementById("is_rtr_chk_box");
if (is_rtr != null) {
  is_rtr.addEventListener("click", function() {on_click_rtr_checkbox()});
  // Call this fxn on load/refresh to ensure correct behavior
  on_click_rtr_checkbox();

} else  {
  alert ("DEVELOPER ERROR: is_rtr_chk_box MIA!")
}

var decode_msg_stream_btn = document.getElementById ("decode_can_msg_stream_btn");
if (decode_msg_stream_btn != null)  {
  decode_msg_stream_btn.addEventListener ("click", function() {on_click_decode()});

} else  {
  alert ("DEVELOPER ERROR: decode_can_msg_stream_btn MIA!")
}

// This button will be used for testing only
var make_randomized_test_stream_btn = document.getElementById ("gen_rand_stream_btn");
if (make_randomized_test_stream_btn != null)  {
  make_randomized_test_stream_btn.addEventListener ("click", function() {on_click_test_stream()});
} else  {
  alert ("DEVELOPER ERROR: gen_rand_stream_btn MIA!")
}

/**************************************************************
 * <END> REGISTER EVENT HANDLERS
***************************************************************/

/**************************************************************
 * GLOBAL SCOPE
***************************************************************/
var can_bus_intro_txt_box = document.getElementById ("can_bus_intro_txt_box");
if (can_bus_intro_txt_box != null)  {
  can_bus_intro_txt_box.value = "The Controller Area Network, or CAN bus, reduces both wire length and complexity for control systems in cars. ";
  can_bus_intro_txt_box.value += "\nBefore CAN, cars had many point-to-point connections between user inputs and the devices that were controlled. ";
 
  can_bus_intro_txt_box.value += "\nA simplified explanation of the CAN bus is that of a network wire that goes around the entirety of the car, and devices ";
  can_bus_intro_txt_box.value += "\nconnect to this wire, and receive messages from embedded controllers that amount to commands to devices or requests ";
  can_bus_intro_txt_box.value += "\nfor information from them.";
  can_bus_intro_txt_box.value += "\n";
 
  can_bus_intro_txt_box.value += "\nDue to its low cost, data integrity in noisy environments and ready availability of hardware transceivers and bus analyzers, ";
  can_bus_intro_txt_box.value += "\nthe CAN bus has successfully permeated the auto industry and has expanded into industrial automation and medical equipment. ";
  can_bus_intro_txt_box.value += "\n";
  can_bus_intro_txt_box.value += "\nThe CAN bus transmits data serially, meaning one bit at a time, much the same as on a computer network. ";
  can_bus_intro_txt_box.value += "\nCAN uses differential signaling with two wires to send a single bit to provide clear data transmission in the ";
  can_bus_intro_txt_box.value += "\nelectrically noisy environment of a running car. ";
  can_bus_intro_txt_box.value += "\nA dominant logical 0 is represented by one wire with a HIGH voltage; the other with LOW voltage.";
  can_bus_intro_txt_box.value += "\nA recessive logical 1 is represented by both wires at the same voltage. ";
  can_bus_intro_txt_box.value += "\nDifferential signaling is cleaner than single wire data bit transmission because the two wires are compared to one another, ";
  can_bus_intro_txt_box.value += "\ninstead of a single wire compared with a ground plane voltage, which could shift and possibly cause data corruption. ";
  can_bus_intro_txt_box.value += "\nSince the differential pair are compared to one another, any ground plane shifting will affect both equally. ";

  can_bus_intro_txt_box.value += "\nCAN uses bit stuffing to reduce the probability of data transmission errors, and cyclic redundancy checks to greatly increase ";
  can_bus_intro_txt_box.value += "\nthe probability of catching data errors while keeping the non-data overhead in each frame to a reasonable minimum. ";
  can_bus_intro_txt_box.value += "\n";

}