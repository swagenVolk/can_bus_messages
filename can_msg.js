/**************************************************************
 * GLOBAL
 * TODO: 
 * Generate CAN message with field names aligned underneath 
 * corresponding bit values - padded with spaces, or use colors?
 *  Not getting a newline
 *  Alignment is off
 *  Should I have separate string field values?
 * Do stuff bits get a color, or [x|y]?  Latter might be better
 * for visibility continuity
 * RTR|SRR
 * CRC
***************************************************************/
// From https://en.wikipedia.org/wiki/Endianness :
// Many IETF RFCs use the term network order, meaning the order of transmission for bytes over the wire in network protocols. 
// Among others, the historic RFC 1700 defines the network order for protocols in the Internet protocol suite to be big-endian.
// However, not all protocols use big-endian byte order as the network order. The Server Message Block (SMB) protocol uses 
// little-endian byte order. In CANopen, multi-byte parameters are always sent least significant byte first (little-endian). 
// The same is true for Ethernet Powerlink.
// TODO: DLC? CRC?
var is_data_index_order_big_endian = true;
var is_data_in_bytes_big_endian = true;

var BASE_MSG_FLD_LEN = 11;
var EXT_MSG_FLD_LEN = 18;
var BASE_MSG_MASK = 0b11111111111;
var EXT_MSG_MASK_UPPER = 0b11111111111000000000000000000; 
var EXT_MSG_MASK_LOWER = 0b111111111111111111;
var STUFF_TRIGGER_CNT = 5;

class presentationStr {
  data_str;
  field_guide;

  constructor() {
    this.data_str =    "";
    this.field_guide = "";
  }

}

class passByRefNum  {
  // Hacky class object to allow for passing by reference
  // TODO: I'm sure there's a better way to do this
  val;

  constructor (num_val) {
    this.val = num_val;
  }
}

class canMsgFields  {
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

  constructor (msg_id, is_rtr, dlc, data) {
    // Start Of Frame is always DOMINANT (0)
    this.SOF = 0b0;
    var max_11bit_id = Math.pow (2, BASE_MSG_FLD_LEN) - 1;
    if (msg_id <= max_11bit_id)
      // 0 (DOMINANT) indicates 11-bit message ID
      this.IDE = 0;
    else
      // 1 (recessive) indicates extended format 29-bit message ID
      this.IDE = 1; 

    // Message ID *MUST* be in big-endian, network order for address conflict resolution to work
    if (this.IDE == 0) {
      this.MSG_ID = msg_id;
      this.EXT_MSG_ID = 0;
    
    } else  {
      this.MSG_ID = (msg_id & EXT_MSG_MASK_UPPER) >> EXT_MSG_FLD_LEN;
      this.EXT_MSG_ID = (msg_id & EXT_MSG_MASK_LOWER);
    }

    this.RTR = is_rtr ? 0b1 : 0b0;
    // Must be recessive (1) 
    this.SRR = 0b1;

    // Reserved bits which must be set dominant (0), but accepted as either dominant or recessive 
    this.r0 = 0b0;
    this.r1 = 0b0;

    if (this.RTR == 0b1)  {
      // NO DATA for a Remote Transmission Request (RTR)
      this.DLC = 0b0000;

    } else {
      // TODO: DLC is a 4-bit field. So is it [big|little]-endian?
      this.DLC = dlc;

      this.DATA = new Uint8Array(dlc);

      for (var idx = 0; idx < dlc; idx++) {
        this.DATA[idx] = data[idx];
      }
    }

    // TODO: How is this calculated?
    this.CRC = 0b01010101;

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
  return fld_data;

  for (var idx = 0; idx < fld_data.length; idx++) {
    var curr_char = fld_data[idx];

    if (curr_char == ' ')  {
      stuffed_str += curr_char;
    
    } else if (curr_bit == 'a' || curr_bit == 'b')  {
      var curr_bit = curr_char == 'a' ? 0 : 1;
      var other_bit = curr_bit == 0 ? 1 : 0;
      stuffed_str += curr_char;
      
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
  // TODO: Add byte|nibble blanks
  var tmp_str = "";
  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.MSG_ID, 4, 11), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "ID", tmp_str, 11);

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
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.EXT_MSG_ID, 4, 18), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "EXT_ID", tmp_str, 18);
    //   RTR
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.RTR, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "RTR", tmp_str, 1);
    //   r1
    tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.r1, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
    append_presentation_strings (msg_descr, "r1", tmp_str, 1);
  }

  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.r0, 1, 1), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "r0", tmp_str, 1);

  tmp_str = bit_stuff_string (make_readable_bit_string (can_msg_data.DLC, 4, 4), prev_bit, seq_bit_cnt, total_stuff_cnt);
  append_presentation_strings (msg_descr, "DLC", tmp_str, 4);
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
  var users_msg_id = document.getElementById("msg_id_txt_box").value;
  return num_in_range ("Message ID", users_msg_id, 0, 0x1FFFFFFF, msg_id_val);

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
 * Validate user's input into fields for generating a CAN bus
 * message.
***************************************************************/
function gen_can_msg_btn_pressed (event) {
  var accum_err_msg = "";

  var generated_msg_txt_box = document.getElementById("gen_can_msg_txt_box");
  if (generated_msg_txt_box != null)  {
    generated_msg_txt_box.value = "";
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
    can_msg_data = new canMsgFields (msg_id.val, get_rtr_checked(), calculated_dlc.val, data_array)
    make_can_msg_str (can_msg_data, msg_descr);

    if (generated_msg_txt_box != null)  {
      generated_msg_txt_box.value = msg_descr.data_str + "\n\n" + msg_descr.field_guide;
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
 * Register event handler(s)
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
