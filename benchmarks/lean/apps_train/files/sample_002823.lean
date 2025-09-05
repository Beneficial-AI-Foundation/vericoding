Define two functions: `hex_to_bin` and `bin_to_hex` (or `hexToBin` and `binToHex`)

# hex_to_bin

Takes a hexadecimal string as an argument .

**Note:** This string can contain upper or lower case characters and start with any amount of zeros.

Returns the binary representation (without leading zeros) of the numerical value of the hexadecimal string.

Examples:

```
"00F"    -->  "1111"
"5"      -->  "101"
"00000"  -->  "0"
"04D2"   -->  "10011010010"
```

# bin_to_hex

Takes a binary string (with or without leading zeros) as an argument .

Returns the hexadecimal representation of the numerical value of the binary string.

**Note:** Any non-numerical characters should be lower case

Examples:

```
"1111"         -->  "f"
"000101"       -->  "5"
"10011010010"  -->  "4d2"
```

**Note:** You can assume all arguments are valid so there is no need for error checking.

Oh, and I've disabled a few things.

Any feedback would be much appreciated

def bin_to_hex (b : String) : String := sorry 
def hex_to_bin (h : String) : String := sorry

def is_hex_digit (c : Char) : Bool := sorry 

-- Helper for theorem statement

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
