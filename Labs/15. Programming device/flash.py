# -----------------------------------------------------------------------------
# Project Name   : Architectures of Processor Systems (APS) lab work
# Organization   : National Research University of Electronic Technology (MIET)
# Department     : Institute of Microdevices and Control Systems
# Author(s)      : Andrei Solodovnikov
# Email(s)       : hepoh@org.miet.ru
#
# See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
# ------------------------------------------------------------------------------
#
import argparse
import serial

parser = argparse.ArgumentParser()
parser.add_argument("instr", type=str, help="File for instr mem initialization")
parser.add_argument("comport", type=str, help="COM-port name")
parser.add_argument("-d", "--data",  type=str, help="File for data mem initialization")
parser.add_argument("-c", "--color", type=str, help="File for color mem initialization")
parser.add_argument("-t", "--tiff",  type=str, help="File for tiff mem initialization")

args = parser.parse_args()

def parse_file(fname: str, base: int = 16, chars_in_byte: int = 2, start_addr: int = None) -> dict:
  res_bytes=b''
  bytes_map = {}
  with open(fname, 'r') as fp:
    for line in fp:
      if line[0] == '@':
        if res_bytes:
          assert(start_addr is not None)
          bytes_map[start_addr] =  res_bytes[::-1]
          res_bytes = b''
        start_addr = int(line[1:], 16)
      else:
        for word in line.split():
          res_bytes += bytes(int(word,base).to_bytes(len(word)//chars_in_byte,"little"))
    assert(start_addr is not None)
    bytes_map[start_addr] = res_bytes[::-1]
  return bytes_map

def flash(data: bytes, port: serial.Serial, start_addr: int):

  addr_bytes = start_addr.to_bytes(4, "big")
  port.write(addr_bytes)

  ready_msg = port.read(40)
  ready_msg_str = ready_msg.decode("ascii")
  print(ready_msg_str)
  assert(ready_msg_str == "ready for flash staring from 0x{:08x}\n".format(start_addr))

  data_len = len(data)
  data_len_bytes = data_len.to_bytes(4, "big")
  port.write(data_len_bytes)

  data_len_ack_bytes = port.read(4)
  data_len_ack = int.from_bytes(data_len_ack_bytes,"big")
  print("0x{:08x}".format(data_len_ack))
  assert(data_len_ack == data_len)

  port.write(data)

  print("Sent {:08x} bytes".format(data_len))

  data_flash_ack = port.read(57)
  data_flash_ack_str = data_flash_ack.decode("ascii")
  print(data_flash_ack_str)
  assert(data_flash_ack_str == "finished write 0x{:08x} bytes starting from 0x{:08x}\n".format(data_len, start_addr))



# Main block

inst_file = args.instr
data_file = args.data
color_file= args.color
tiff_file = args.tiff
com       = args.comport

instr = parse_file(inst_file, start_addr=0)

if data_file:
  data  = parse_file(data_file)
else:
  data  = {}

if color_file:
  color  = parse_file(color_file)
else:
  color  = {}

if tiff_file:
  tiff  = parse_file(tiff_file, 2, 8)
else:
  tiff  = {}


ser = serial.Serial(
    port=com,
    baudrate=115200,
    parity=serial.PARITY_EVEN,
    stopbits=serial.STOPBITS_ONE,
    bytesize=serial.EIGHTBITS,
    timeout=None
)

for ass_arr in [instr, data, color, tiff]:
  for addr, bytes_list in ass_arr.items():
    flash(bytes_list, ser, addr)

ser.write(bytes([255]*4))
