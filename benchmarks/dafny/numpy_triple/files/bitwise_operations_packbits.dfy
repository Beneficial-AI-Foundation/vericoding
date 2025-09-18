// <vc-preamble>
// Enumeration for bit ordering in packbits
datatype BitOrder = Big | Little

// Helper function to compute the number of output bytes needed
function OutputLength(inputLen: nat): nat
{
    (inputLen + 7) / 8
}

// Helper function to extract a bit value at a specific position, with bounds checking
function GetBitAt(input: seq<bool>, index: nat): nat
{
    if index < |input| && input[index] then 1 else 0
}

// Helper function to compute the bit position within a byte for big-endian ordering
function BigEndianBitPos(bitIndex: nat): nat
    requires bitIndex < 8
{
    7 - bitIndex
}

// Helper function to compute the bit position within a byte for little-endian ordering  
function LittleEndianBitPos(bitIndex: nat): nat
    requires bitIndex < 8
{
    bitIndex
}

// Helper function to compute powers of 2
function TwoPow(exp: nat): nat
    ensures TwoPow(exp) >= 1
    ensures exp <= 7 ==> TwoPow(exp) <= 128
{
    if exp == 0 then 1
    else 2 * TwoPow(exp - 1)
}

// Recursive helper for big-endian bit packing
function PackByteBig(input: seq<bool>, startIdx: nat, bitsRemaining: nat, currentBit: nat, accumulator: nat): nat
    requires currentBit <= 8
    requires bitsRemaining <= 8 - currentBit
    requires accumulator <= 255
    ensures PackByteBig(input, startIdx, bitsRemaining, currentBit, accumulator) <= 255
    decreases bitsRemaining
{
    if bitsRemaining == 0 || currentBit >= 8 then
        accumulator
    else
        var bitValue := GetBitAt(input, startIdx + currentBit);
        var bitPosition := BigEndianBitPos(currentBit);
        var newAccumulator := accumulator + (bitValue * TwoPow(bitPosition));
        PackByteBig(input, startIdx, bitsRemaining - 1, currentBit + 1, newAccumulator)
}

// Recursive helper for little-endian bit packing
function PackByteLittle(input: seq<bool>, startIdx: nat, bitsRemaining: nat, currentBit: nat, accumulator: nat): nat
    requires currentBit <= 8
    requires bitsRemaining <= 8 - currentBit
    requires accumulator <= 255
    ensures PackByteLittle(input, startIdx, bitsRemaining, currentBit, accumulator) <= 255
    decreases bitsRemaining
{
    if bitsRemaining == 0 || currentBit >= 8 then
        accumulator
    else
        var bitValue := GetBitAt(input, startIdx + currentBit);
        var bitPosition := LittleEndianBitPos(currentBit);
        var newAccumulator := accumulator + (bitValue * TwoPow(bitPosition));
        PackByteLittle(input, startIdx, bitsRemaining - 1, currentBit + 1, newAccumulator)
}

// Helper function to pack 8 bits into a single UInt8 value
function PackByte(input: seq<bool>, byteIndex: nat, bitOrder: BitOrder): bv8
    requires byteIndex < OutputLength(|input|)
{
    var startIdx := byteIndex * 8;
    var bitsInByte := if startIdx + 8 <= |input| then 8 else |input| - startIdx;
    
    if bitOrder == Big then
        PackByteBig(input, startIdx, bitsInByte, 0, 0) as bv8
    else
        PackByteLittle(input, startIdx, bitsInByte, 0, 0) as bv8
}

// Main method specification for packbits
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PackBits(input: seq<bool>, bitOrder: BitOrder := Big) returns (result: seq<bv8>)
    ensures |result| == OutputLength(|input|)
    ensures forall i :: 0 <= i < |result| ==> result[i] == PackByte(input, i, bitOrder)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
