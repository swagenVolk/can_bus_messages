/**************************************************************
 * GLOBAL
 * TODO: 
 * Get it working with known good messages
 *  Passing vs. failing info: DATA ordering; both hex and decimal values? Value of RAW CAN msg? Take out new lines?
 * Calculate CRC
 *  Is it being done correctly?  What about additional 0s added at end?
 *  Last bit is the CRC delimiter, which must be recessive (0)
 *  Need to bit stuff the CRC with the execption of the delimiter
 *  Display 15-bit CRC.  Break delimiter out?
 * Handle error conditions
 *  Fail but continue eating message
 *  Hard fail; look for 10 floats in a row
 * Test extended
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
var CRC_FLD_LEN = 16;
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
    var final_mask = 0x1;

    for (idx = 0; idx < this.poly_bit_size; idx++)  {
      // Pad with additional [0]{poly_bit_size} bits and returned computed CRC
      // TODO: Some specify doing this; others don't
      this.next_bit_crc_calc (0);
      final_mask <<= 0x1;
      final_mask |= 0x1;
    }

    // Make sure our final computed CRC is limited by polynomial size + 1
    this.computed_crc &= final_mask;
    // Last bit of the CRC field is the delimiter, and it must be recessive (1)
    this.computed_crc |= 0x1;
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

  constructor() {
    this.data_str =    "";
    this.field_guide = "";
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
var GET_ACK = 10;
var GET_EOF = 11;
var GET_IFS = 12;
var MSG_FAILED = 13;
var MSG_END_OK = 14;

class canMsgParseState {
  can_msg_stream;
  curr_str_idx;
  curr_msg_number;

  usr_msg_raw;
  usr_msg_01_stuffed;
  usr_msg_xy_stuffed;

  curr_msg_state;
  curr_hdr_bit_val;
  prev_hdr_bit_val;
  num_consecutive;
  num_stuffed;
  is_failed;
  failure_msg;
  msg_id;
  msg_id_bit_cnt;
  extended_msg_id;
  extended_msg_id_bit_cnt;
  is_rtr;
  is_extended;
  r0_val;
  r1_val;
  data_length_code;
  num_dlc_bits;
  data;
  num_data_bytes_expected;
  num_data_bytes_actual;
  senders_crc;
  calculated_crc;
  num_crc_bits;
  is_ack_valid;
  num_ack_bits;
  is_eof_valid;
  num_eof_bits;
  is_ifs_valid;
  num_ifs_bits;
  is_stuffing_on;
  line_num;
  column;
  SOF_start_line;
  SOF_start_col;
  is_end_of_stream;
  parserCrc;

  reset_for_single_msg ()  {
    this.curr_msg_state = GET_SOF;
    this.SOF_start_line = 0;
    this.SOF_start_col = 0;
    
    // Bit position in the header; ignores bit stuffing;
    this.curr_hdr_bit_val = 0;
    this.prev_hdr_bit_val = 0;
    this.num_consecutive = [0,0];
    this.num_stuffed = [0,0];
    this.is_failed = false;
    this.failure_msg = "";
    this.msg_id = 0;
    this.msg_id_bit_cnt = 0;
    this.extended_msg_id = 0;
    this.extended_msg_id_bit_cnt = 0;
    this.is_rtr = false;
    this.is_extended = false;
    this.r0_val = 0;
    this.r1_val = 0;
    this.data_length_code = 0;
    this.num_dlc_bits = 0;
    this.data = [0,0,0,0,0,0,0,0];
    this.senders_crc = 0;
    this.calculated_crc = 0;
    this.is_ack_valid = true;
    this.num_data_bytes_expected = 0;
    this.num_data_bytes_actual = 0;
    this.num_crc_bits = 0;
    this.num_ack_bits = 0;
    this.is_eof_valid = true;
    this.num_eof_bits = 0;
    this.is_ifs_valid = true;
    this.num_ifs_bits = 0;
    this.is_stuffing_on = true;
    this.usr_msg_raw = "";
    this.usr_msg_01_stuffed = "";
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
  mark_failure (error_msg)  {
    this.is_failed = true;
    this.failure_msg = error_msg;
  }

  /* ***************************************************************************
  * Utility fxn to print out the current message state
  * *************************************************************************** */
  can_msg_info_str ()  {
    var info_str = "";

    info_str += "\nCAN Message #" + this.curr_msg_number;
    info_str += "\nSOF starts at line:column " + this.SOF_start_line + ":" + this.SOF_start_col;
    info_str += "\nRaw CAN msg =    " + this.usr_msg_raw;
    info_str += "\nMsg XY stuffed = " + this.usr_msg_xy_stuffed;
    info_str += "\nMsg 01 stuffed = " + this.usr_msg_01_stuffed;

    if (this.is_failed) {
      info_str += "\nLine:column = " + this.line_num + ":" + this.column;
      info_str += "\nFailure message = " + this.failure_msg;
      info_str += "\ncurr_msg_state = " + this.curr_msg_state;
      info_str += "\ncurr_hdr_bit_val = " + this.curr_hdr_bit_val;
      info_str += "\nprev_hdr_bit_val = " + this.prev_hdr_bit_val;
      info_str += "\nconsecutive 0 count = " + this.num_consecutive[0];
      info_str += "\nconsecutive 1 count = " + this.num_consecutive[1];
    }
    info_str += "\nmsg_id = " + make_hex_and_decimal(this.msg_id);
    info_str += "\nextended_msg_id = " + make_hex_and_decimal (this.extended_msg_id);
    info_str += "\nis_rtr = " + this.is_rtr;
    info_str += "\nis_extended = " + this.is_extended;
    info_str += "\nr0_val = " + this.r0_val;
    info_str += "\nr1_val = " + this.r1_val;
    info_str += "\ndata_length_code = " + make_hex_and_decimal(this.data_length_code);
    info_str += "\ndata = ";

    for (var idx = this.data_length_code - 1; idx >= 0; idx--)  {
      // Display big-endian with most significant bytes 1st
      info_str += "[" + make_hex_and_decimal (this.data[idx]) + "] ";
    }

    info_str += "\nsenders_crc = " + make_hex_and_decimal (this.senders_crc);

    if (this.is_failed) {
      info_str += "\nis_ack_valid = " + this.is_ack_valid;
      info_str += "\nnum_data_bytes_expected = " + this.num_data_bytes_expected;
      info_str += "\nnum_data_bytes_actual = " + this.num_data_bytes_actual;
      info_str += "\nnum_crc_bits = " + this.num_crc_bits;
      info_str += "\nis_eof_valid = " + this.is_eof_valid;
      info_str += "\nnum_eof_bits = " + this.num_eof_bits;
      info_str += "\nis_ifs_valid = " + this.is_ifs_valid;
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

      if (this.curr_msg_state == GET_SOF)  {
        if (curr_bit == 0)  {
          this.SOF = 0;
          this.curr_msg_state = GET_MSG_ID;
          this.SOF_start_line = this.line_num;
          this.SOF_start_col = this.column;
          this.parserCrc.add_bits_to_crc (new numPair (this.SOF, 1));
        }

      } else if (this.curr_msg_state == GET_MSG_ID)  {
        this.msg_id <<= 1;
        this.msg_id |= this.curr_hdr_bit_val;
        this.msg_id_bit_cnt++;
        if (this.msg_id_bit_cnt == ID_FLD_LEN)  {
          this.parserCrc.add_bits_to_crc (new numPair (this.msg_id, ID_FLD_LEN));
          this.curr_msg_state = GET_RTR;
        }
      
      } else if (this.curr_msg_state == GET_RTR) {
        if (this.curr_hdr_bit_val == 0)
            // RTR bit is DOMINANT
            this.is_rtr = true;
        else
            this.is_rtr = false;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* RTR */, 1));
        this.curr_msg_state = GET_R1;

      } else if (this.curr_msg_state == GET_IDE) {
        if (this.curr_hdr_bit_val == 0)  {
            // IDE bit is DOMINANT
            this.is_extended = false;
            this.curr_msg_state = GET_R0;
        } else {
            this.is_extended = true;
            this.curr_msg_state = GET_XID;
        }
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* IDE */, 1));

      } else if (this.curr_msg_state == GET_XID) {
        this.extended_msg_id <<= 1;
        this.extended_msg_id |= this.curr_hdr_bit_val;
        this.extended_msg_id_bit_cnt++;
        if (this.extended_msg_id_bit_cnt == XID_FLD_LEN)  {
          this.curr_msg_state = GET_RTR;
          this.parserCrc.add_bits_to_crc (new numPair (this.extended_msg_id, XID_FLD_LEN));

        }

      } else if (this.curr_msg_state == GET_R0)  {
        this.r0_val = this.curr_hdr_bit_val;
        this.curr_msg_state = GET_DLC;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* RO */, 1));

      } else if (this.curr_msg_state == GET_R1)  {
        this.r1_val = this.curr_hdr_bit_val;
        this.curr_msg_state = GET_R0;
        this.parserCrc.add_bits_to_crc (new numPair (this.curr_hdr_bit_val /* R1 */, 1));

      } else if (this.curr_msg_state == GET_DLC) {
        this.num_dlc_bits++;
        this.data_length_code |= (this.curr_hdr_bit_val << (DLC_FLD_LEN - this.num_dlc_bits));

        if (this.num_dlc_bits == DLC_FLD_LEN)  {
          // Done processing the Data Length Code field
          
          if (this.data_length_code > 0) {
            if (this.data_length_code > 8)
              // There are 4 bits, so 9-15 can be represented, but our ceiling is still 8
              this.data_length_code = 8;

            // TODO: How should the 9-15 values be handled regarding the CRC?
            this.parserCrc.add_bits_to_crc (new numPair (this.data_length_code, DLC_FLD_LEN));
            this.curr_msg_state = GET_DATA;
            this.num_data_bytes_expected = this.data_length_code * 8;
            
          } else {
            this.curr_msg_state = GET_CRC;
          }
        }

      } else if (this.curr_msg_state == GET_DATA)  {
          var data_idx = Math.floor(this.num_data_bytes_actual/8);
          var chunk = this.data[data_idx];
          chunk <<= 1;
          chunk |= this.curr_hdr_bit_val;
          this.data[data_idx] = chunk;
          this.parserCrc.add_bits_to_crc (new numPair (this.data[data_idx], 8));
          this.num_data_bytes_actual += 1;

          if (this.num_data_bytes_actual == this.num_data_bytes_expected)
              this.curr_msg_state = GET_CRC;

      } else if (this.curr_msg_state == GET_CRC) {
        this.num_crc_bits += 1;
        if (this.num_crc_bits == 1)
          // TODO: Questions remain on how this is calculated
          // TODO: In case of actual bit-banging, is there a SMRT way to do
          // this calculation asynchronously? Does it even matter?
          this.calculated_crc = this.parserCrc.get_computed_crc_final();

        this.senders_crc <<= 0x1;
        // Add bits in INCLUDING ending delimiter
        this.senders_crc |= this.curr_hdr_bit_val;

        if (this.num_crc_bits == CRC_FLD_LEN) {
          if (this.curr_hdr_bit_val != 1) {
            this.mark_failure("FAILURE: Expected CRC delimiter to be RECESSIVE (1)!");
          } else  {
            this.curr_msg_state = GET_ACK;
            if (this.senders_crc != this.calculated_crc)
              this.mark_failure ("FAILURE: calculated CRC does NOT match sender's CRC! (" + make_hex_and_decimal (this.calculated_crc) + " <> " + make_hex_and_decimal (this.senders_crc) + ")");
          }
        } else if (this.num_crc_bits == (CRC_FLD_LEN - 1))  {
          // The CRC Delimiter is up next and bit stuffing is turned off
          this.is_stuffing_on = false;
        }

      } else if (this.curr_msg_state == GET_ACK) {
        this.num_ack_bits += 1;
        if (this.num_ack_bits == 1 && this.curr_hdr_bit_val != 1) {
          // ACK must be RECESSIVE
          this.is_ack_valid = false;
          this.mark_failure("FAILURE: ACK must be RECESSIVE (1)!");

        } else if (this.num_ack_bits == ACK_FLD_LEN)  {
          if (this.curr_hdr_bit_val != 1)  {
            // ACK delimiter must be RECESSIVE
            this.is_ack_valid = false;
            this.mark_failure("FAILURE: ACK delimiter must be RECESSIVE (1)!");
          } else {
              // ACK delimiter must be RECESSIVE
              this.is_ack_valid = true;
          }
          this.curr_msg_state = GET_EOF;
        }
      } else if (this.curr_msg_state == GET_EOF) {
          if (this.curr_hdr_bit_val == 0)
              this.is_eof_valid = false;
          
          this.num_eof_bits += 1;
          
          if (this.num_eof_bits == EOF_FLD_LEN)
              this.curr_msg_state = GET_IFS;

      } else if (this.curr_msg_state == GET_IFS) {
          if (this.curr_hdr_bit_val == 0)
              this.is_ifs_valid = false;
          
          this.num_ifs_bits += 1;
          
          if (this.num_ifs_bits == IFS_FLD_LEN)
              // TODO: Might need to add a "quiescent" state.....maybe
              this.curr_msg_state = MSG_END_OK;

      } else {
        this.mark_failure("INTERNAL ERROR: Fell all the way through to No Man's Land!");
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
      
      if (this.curr_msg_state > GET_SOF && this.curr_msg_state < MSG_FAILED && this.curr_msg_state < MSG_END_OK) {
        if (curr_bit_val != this.prev_hdr_bit_val) {
          if (this.num_consecutive[other_idx] == STUFF_TRIGGER_CNT)  {
            // This is a stuffed bit; let the caller know to toss it!
            is_stuffed = true;
            this.num_stuffed[curr_bit_val] += 1;

            if (curr_bit_val == 0)  {
              this.usr_msg_xy_stuffed += "x";
              this.usr_msg_01_stuffed += "0";

            } else if (curr_bit_val == 1) {
              this.usr_msg_xy_stuffed += "y";
              this.usr_msg_01_stuffed += "1";
            
            }  else {
              this.usr_msg_xy_stuffed += "Z";
              this.usr_msg_01_stuffed += "?";

            }

            this.num_consecutive[other_idx] = 0;
            this.num_consecutive[curr_bit_val] = 1;
          
          } else  {
            // Polarity has flipped; reset our counters
            this.num_consecutive[other_idx] = 0;
            this.num_consecutive[curr_bit_val] = 1;
          }
      
        } else if (curr_bit_val == this.prev_hdr_bit_val)  {
          if (this.num_consecutive[curr_bit_val] == (STUFF_TRIGGER_CNT + 1))
              this.mark_failure("Expected a bit stuffed " + other_idx);
          else
              this.num_consecutive[curr_bit_val] += 1;
        }
      
      } else {
        // Account for the very 1st SOF bit, which should be DOMINANT (0)
        this.num_consecutive[curr_bit_val] = 1;
        this.num_consecutive[other_idx] = 0;
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
    this.usr_msg_xy_stuffed += bit_val;
    this.usr_msg_01_stuffed += bit_val;

    if (this.is_stuffing_on) {
      if (!this.is_stuff_bit (bit_val)) {
        this.eat_non_stuffed_bit (bit_val);
      }
        
    } else {
      // Bit stuffing OFF; pass value along to be handled normally
      this.eat_non_stuffed_bit(bit_val);
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

    this.usr_msg_01_stuffed = "";
    this.usr_msg_xy_stuffed = "";
    var next_char;

    while (this.curr_msg_state != MSG_END_OK && this.curr_msg_state != MSG_FAILED && !this.is_failed && !this.is_end_of_stream) {
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
      
      } else if ((next_char == '\s' || next_char == '\t') && this.usr_msg_raw.length > 0)  {
        // Don't start adding until the actual message's SOF
        this.usr_msg_raw += next_char;
        this.column++;

      } else  {
        this.column++;

      }

      // Marching ever forward towards completion
      this.curr_str_idx++;

      if (this.curr_str_idx == this.can_msg_stream.length)
        this.is_end_of_stream = true;
    }

    if (this.SOF_start_line > 0 || this.curr_msg_state == MSG_END_OK || this.curr_msg_state == MSG_FAILED)
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
  ACK;
  EOF;
  IFS;

  generatorCrc;

  constructor (msg_id, is_rtr, dlc, data) {
    this.generatorCrc = new crcHolder(CRC_POLYNOMIAL);
    // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
    // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
    
    // Start Of Frame is always DOMINANT (0)
    this.SOF = 0;
    this.generatorCrc.add_bits_to_crc (new numPair (this.SOF, 1));

    var max_11bit_id = Math.pow (2, ID_FLD_LEN) - 1;
    
    if (msg_id <= max_11bit_id) {
      // 0 (DOMINANT) indicates 11-bit message ID
      this.IDE = 0;
      // Message ID *MUST* be in big-endian, network order for address conflict resolution to work
      this.MSG_ID = msg_id;
      this.EXT_MSG_ID = 0;

    } else  {
      // 1 (recessive) indicates extended format 29-bit message ID
      this.IDE = 1; 
      // mmmmmmmmmmmxxxxxxxxxxxxxxxxxx
      this.MSG_ID = (msg_id & EXT_MSG_MASK_U11) >> XID_FLD_LEN;
      this.EXT_MSG_ID = (msg_id & EXT_MSG_MASK_L18);

    }

    this.generatorCrc.add_bits_to_crc (new numPair (this.MSG_ID, ID_FLD_LEN));

    this.RTR = is_rtr ? 1 : 0;
    // Must be recessive (1) 
    this.SRR = 1;

    if (this.IDE == 0)
      // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
      this.generatorCrc.add_bits_to_crc (new numPair (this.RTR, 1));

    else
      // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
      this.generatorCrc.add_bits_to_crc (new numPair (this.SRR, 1));

    this.generatorCrc.add_bits_to_crc (new numPair (this.IDE, 1));

    // Reserved bits which must be set dominant (0), but accepted as either dominant or recessive 
    this.r0 = 0;
    this.r1 = 0;

    if (this.IDE == 1)  {
      // Standard: [SOF|ID|RTR|IDE|r0|DLC|DATA|CRC|ACK|EOF|IFS]
      // Extended: [SOF|ID|SRR|IDE|EXT_ID|RTR|r1|r0|DLC|DATA|CRC|ACK|EOF|IFS]
      this.generatorCrc.add_bits_to_crc (new numPair (this.EXT_MSG_ID, XID_FLD_LEN));
      this.generatorCrc.add_bits_to_crc (new numPair (this.RTR, 1));
      this.generatorCrc.add_bits_to_crc (new numPair (this.r1, 1));
    }
    
    this.generatorCrc.add_bits_to_crc (new numPair (this.r0, 1));


    if (this.RTR == 0b1)  {
      // NO DATA for a Remote Transmission Request (RTR)
      this.DLC = 0;

    } else {
      // TODO: DLC is a 4-bit field. So is it [big|little]-endian?
      this.DLC = dlc;

    }

    this.generatorCrc.add_bits_to_crc (new numPair (this.DLC, DLC_FLD_LEN));

    if (this.DLC > 0) {
      this.DATA = new Uint8Array(dlc);

      for (var idx = 0; idx < dlc; idx++) {
        this.DATA[idx] = data[idx];
        // TODO: Endian-ness of DATA?
        this.generatorCrc.add_bits_to_crc (new numPair (data[idx], 8));
      }
    }

    // TODO: Questions remain on how this is calculated
    this.CRC = this.generatorCrc.get_computed_crc_final();

    // Transmitter sends recessive (1) and any receiver can assert a dominant (0)
    // Followed by ACK delimiter (recessive)
    this.ACK = 0b11;

    // Must be recessive (1) 
    this.EOF = 0b1111111;

    // Must be recessive (1) 
    this.IFS = 0b111;
  }
}

/**************************************************************
 * Modifies the passed in field if stuff bits are needed
***************************************************************/
function bit_stuff_string (fld_data, prev_bit, seq_bit_cnt, total_stuff_cnt)  {
  var stuffed_str = "";

  for (var idx = 0; idx < fld_data.length; idx++) {
    var curr_bit = fld_data[idx];

    if (curr_bit == ' ')  {
      stuffed_str += curr_bit;
    
    } else if (curr_bit == '0' || curr_bit == '1')  {
      stuffed_str += curr_bit;
      var other_bit = curr_bit == 0 ? 1 : 0;
      
      if (prev_bit.val == curr_bit) {
        seq_bit_cnt[curr_bit] += 1;

        if (seq_bit_cnt[curr_bit] == STUFF_TRIGGER_CNT) {
          // Stuffed 0 -> x; stuffed 1 -> y
          stuffed_str += (other_bit == 0) ? 'x' : 'y'
          total_stuff_cnt[other_bit] += 1;
          seq_bit_cnt[curr_bit] = 0;
          seq_bit_cnt[other_bit] = 1;
        }

      } else  {
        // The bit has flipped!
        seq_bit_cnt[other_bit] = 0;
        seq_bit_cnt[curr_bit] = 1;

      }

      prev_bit.val = curr_bit;
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
function append_presentation_strings (descr, field_name, field_value, expected_fld_len) {

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
  append_presentation_strings (msg_descr, "SOF", "0", 1);

  // MSG_ID
  var tmp_str = "";
  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.MSG_ID, ID_FLD_LEN, ID_FLD_LEN), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "ID", tmp_str, ID_FLD_LEN);

  if (can_msg_data.IDE == 1)  {
    // Extended frame - SRR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.SRR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "SRR", tmp_str, 1);

  } else  {
    //   RTR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.RTR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "RTR", tmp_str, 1);
  }
  
  // IDE
  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.IDE, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "IDE", tmp_str, 1);
  
  if (can_msg_data.IDE == 1)  {
    // Extended frame
    //   extended ID
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.EXT_MSG_ID, 4, XID_FLD_LEN), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "EXT_ID", tmp_str, XID_FLD_LEN);
    //   RTR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.RTR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "RTR", tmp_str, 1);
    //   r1
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.r1, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "r1", tmp_str, 1);
  }

  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.r0, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "r0", tmp_str, 1);

  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.DLC, 4, DLC_FLD_LEN), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "DLC", tmp_str, DLC_FLD_LEN);
  // TODO: Add byte|nibble blanks
  if (can_msg_data.DLC > 0) {
    // TODO: FIX can_msg_data.DATA_str = bit_stuff_string (make_readable_bit_string (can_msg_data.DATA_str, 8, can_msg_data.DLC * 8), prev_bit, seq_bit_cnt, total_stuff_cnt);
    // TODO: append_presentation_strings (msg_descr, "DATA", can_msg_data.DATA_str, 4);
  }

  for (var data_idx = 0; data_idx < can_msg_data.DLC; data_idx++) {
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.DATA[data_idx], 8, 8), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, data_idx == 0 ? "DATA" : "", tmp_str, 8);
  }

  // Bit stuffing OFF
  // TODO: CRC - TODO: Add byte|nibble blanks
  tmp_str = make_readable_bit_string (can_msg_data.CRC, 4, 16);
  append_presentation_strings (msg_descr, "CRC", tmp_str, 16);
  
  append_presentation_strings (msg_descr, "ACK", make_readable_bit_string (can_msg_data.ACK, 2, 2), 2);
  append_presentation_strings (msg_descr, "EOF", make_readable_bit_string (can_msg_data.EOF, 7, 7), 7);
  append_presentation_strings (msg_descr, "IFS", make_readable_bit_string (can_msg_data.IFS, 3, 3), 3);

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
  glossary_descr += "\nCRC:    15-bit Cyclic Redundancy Check followed by 1-bit delimiter for detecting transmission errors.";
  glossary_descr += "\nACK:    Acknowledgment; receiver indicates error detection via DOMINANT (0) on 1st of 2 ACK bits.";
  glossary_descr += "\nEOF:    End Of Frame; 7 recessive (1) bits in a row.";
  glossary_descr += "\nIFS:    Inter Frame Space; 3 recessive (1) bits in a row.";

  glossary_descr += "\n\nStuff bits are used to maintain synchronization since there is no clock signal on the CAN bus.";
  glossary_descr += "\nA bit of opposite polarity is inserted after five consecutive bits of the same polarity."
  glossary_descr += "\nIf a transmitter sends 5 [0]s in a row, it must send a [1] stuff bit (de-stuffed by receiver).";
  glossary_descr += "\nIf a transmitter sends 5 [1]s in a row, it must send a [0] stuff bit (de-stuffed by receiver).";
  glossary_descr += "\nBit stuffing is active from SOF to 15-bit calculated CRC and off from the CRC delimiter onwards.";


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
        // TODO: Infinite looping?
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

/**************************************************************
 * <END> REGISTER EVENT HANDLERS
***************************************************************/
