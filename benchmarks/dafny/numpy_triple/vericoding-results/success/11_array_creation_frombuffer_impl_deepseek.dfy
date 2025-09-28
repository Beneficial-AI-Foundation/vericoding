// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

  function inBounds(buffer: seq<bv8>, index: int): bool
  {
    0 <= index < |buffer|
  }

  lemma BufferAccessLemma(buffer: seq<bv8>, count: nat, offset: nat, i: int)
    requires offset + count <= |buffer|
    requires offset < |buffer| || count == 0
    requires 0 <= i < count
    ensures offset + i < |buffer|
  {
  }

// </vc-helpers>

// <vc-spec>
method frombuffer(buffer: seq<bv8>, count: nat, offset: nat) returns (result: seq<bv8>)
    // Buffer must have sufficient bytes for the requested elements
    requires offset + count <= |buffer|
    // Offset must be within buffer bounds when count > 0
    requires offset < |buffer| || count == 0
    // Result has exactly 'count' elements
    ensures |result| == count
    // Elements are read sequentially from the buffer starting at offset
    // Each output element corresponds to exactly one input buffer byte
    ensures forall i :: 0 <= i < count ==> result[i] == buffer[offset + i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation errors by passing parameters to helpers */
  var res := [];
  var idx := 0;
  while idx < count
    invariant 0 <= idx <= count
    invariant |res| == idx
    invariant forall j :: 0 <= j < idx ==> res[j] == buffer[offset + j]
  {
    BufferAccessLemma(buffer, count, offset, idx);
    res := res + [buffer[offset + idx]];
    idx := idx + 1;
  }
  result := res;
}
// </vc-code>
