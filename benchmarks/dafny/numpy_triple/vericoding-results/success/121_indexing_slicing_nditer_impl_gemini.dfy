// <vc-preamble>
// Iterator datatype that holds current position and the data being iterated over
datatype Iterator = Iterator(pos: nat, data: seq<real>)

// Creates an iterator for the given array, starting at position 0
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method nditer(arr: seq<real>) returns (iter: Iterator)
  ensures iter.pos == 0                    // Iterator starts at position 0
  ensures iter.data == arr                 // Original data is preserved unchanged
  ensures iter.pos <= |arr|               // Position is within valid bounds
// </vc-spec>
// <vc-code>
{
  iter := Iterator(0, arr);
}
// </vc-code>
