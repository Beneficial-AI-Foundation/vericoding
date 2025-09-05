Unicode Transformation Format – 8-bit
As the name suggests UTF-8 was designed to encode data in a stream of bytes.

It works by splitting the bits up in multiples of eight. This is achieved by inserting headers to mark in how many bytes the bits were split. If the bits need to be split in two, the header `110` is added as prefix leaving five bits of the byte for the rest of the data. Followed by a continuation byte.

A continuation byte always start with `10` leaving six bits for data.
For a three-way split: the header `1110` is added with two continuation bytes and for four: `11110` with three continuation bytes. The number of ones at the start of the first byte denotes the number of bytes the data was split in.
# Task
Your task is to write two functions:
1. `to_utf8_binary`: which encodes a string to a bitstring using UTF-8 encoding.
2. `from_utf8_binary`: which does the reverse.

- Layout of UTF-8 byte sequences:
```
# BYTES  FIRST CODE POINT  LAST CODE POINT    BYTE 1      BYTE 2      BYTE 3      BYTE 4
    1                   0              127    0xxxxxxx  
    2                 128             2047    110xxxxx    10xxxxxx
    3                2048            65535    1110xxxx    10xxxxxx    10xxxxxx  
    4               65536          1114111    11110xxx    10xxxxxx    10xxxxxx    10xxxxxx
```

# Examples
```
ENCODE
 A  -> 1000001         -> 01000001
 八 -> 101000101101011 -> 1110-0101 10-000101 10-101011

DECODE
 110-00010 10-100111                     -> 10100111          -> §
 11110-000 10-010000 10-001010 10-001100 -> 10000001010001100 -> 𐊌
```
* Spaces and hyphens just for clarity
- https://en.wikipedia.org/wiki/UTF-8#Encoding

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
