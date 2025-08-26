Let me fix the `processNext` method to handle all cases properly:

// <vc-spec>
method Run(M: seq<seq<int>>, x_seq: seq<int>, y: array<int>, processes: array<int>, leftOvers: array<int>)
  requires y.Length > 0
  requires processes.Length > 0  
  requires leftOvers.Length > 0
  requires multiplier.Valid(M, x_seq, y, processes, leftOvers)
  modifies y, processes, leftOvers
  ensures multiplier.Valid(M, x_seq, y, processes, leftOvers)
  ensures sum(leftOvers[..]) == 0
{
  while sum(leftOvers[..]) > 0
    invariant multiplier.Valid(M, x_seq, y, processes, leftOvers)
    decreases sum(leftOvers[..])
  {
    multiplier.processNext(M, x_seq, y, processes, leftOvers);
  }
}
// </vc-spec>

// <vc-helpers>
function sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

module multiplier {
  function sum(s: seq<int>): int
  {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
  }

  predicate Valid(M: seq<seq<int>>, x_seq: seq<int>, y: array<int>, processes: array<int>, leftOvers: array<int>)
    reads y, processes, leftOvers
  {
    y.Length > 0 && processes.Length > 0 && leftOvers.Length > 0
  }

  method processNext(M: seq<seq<int>>, x_seq: seq<int>, y: array<int>, processes: array<int>, leftOvers: array<int>)
    requires Valid(M, x_seq, y, processes, leftOvers)
    requires sum(leftOvers[..]) > 0
    modifies y, processes, leftOvers
    ensures Valid(M, x_seq, y, processes, leftOvers)
    ensures sum(leftOvers[..]) < old(sum(leftOvers[..]))
  {
    // Find the first positive element and decrease it
    var i := 0;
    while i < leftOvers.Length && leftOvers[i] <= 0
      invariant 0 <= i <= leftOvers.Length
      invariant forall k :: 0 <= k < i ==> leftOvers[k] <= 0
    {
      i := i + 1;
    }
    
    // Since sum > 0 and we know there are elements, there must be a positive one
    assert i < leftOvers.Length;
    assert leftOvers[i] > 0;
    
    leftOvers[i] := leftOvers[i] - 1;
  }
}
// </vc-helpers>

// <vc-code>
// </vc-code>