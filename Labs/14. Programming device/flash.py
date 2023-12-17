import argparse
import serial

parser = argparse.ArgumentParser()
parser.add_argument("instr", type=str, help="File for instr mem initialization")
parser.add_argument("comport", type=str, help="COM-port name")
parser.add_argument("-d", "--data",  type=str, help="File for data mem initialization")
parser.add_argument("-t", "--tiff",  type=str, help="File for tiff mem initialization")

args = parser.parse_args()

def parse_file(fname: str, base: int = 16, word_size: int = 2) -> bytes:
  res_bytes=b''
  with open(fname, 'r') as fp:
    for line in fp:
      if line[0] == '@':
        continue
      for word in line.split():
        res_bytes += bytes(int(word,base).to_bytes(len(word)//word_size,"little"))
  return res_bytes[::-1]

def flash(data: bytes, port: serial.Serial, mem_name: str):
  assert(len(mem_name) == 4)

  if data:
    data_len = len(data)
  else:
    data_len = 0
  data_len_bytes = data_len.to_bytes(4, "big")
  port.write(data_len_bytes)

  data_len_ack = port.read(4)
  print(int.from_bytes(data_len_ack,"big"))
  assert(data_len_ack == data_len_bytes)

  if(data):
    port.write(data)

  print("finished write {} mem".format(mem_name))

  data_flash_ack = port.read(10)
  data_flash_ack_str = data_flash_ack.decode("ascii")
  print(data_flash_ack_str)
  assert(data_flash_ack_str == "{} done\n".format(mem_name))



# Main block

inst_file = args.instr
data_file = args.data
tiff_file = args.tiff
com       = args.comport

instr = parse_file(inst_file)

if data_file:
  data  = parse_file(data_file)
else:
  data  = b''

if tiff_file:
  tiff  = parse_file(tiff_file, 2, 8)
else:
  tiff  = b''


ser = serial.Serial(
    port=com,
    baudrate=115200,
    parity=serial.PARITY_EVEN,
    stopbits=serial.STOPBITS_ONE,
    bytesize=serial.EIGHTBITS,
    timeout=None
)

init_msg = ser.read(6)
print(init_msg.decode("ascii"))
assert(init_msg == b'ready\n')

flash(instr, ser, "inst")
flash(data,  ser, "data")
flash(tiff,  ser, "tiff")
