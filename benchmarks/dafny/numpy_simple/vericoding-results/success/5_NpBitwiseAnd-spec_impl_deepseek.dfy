// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

predicate SeqLenMatch<T>(a: seq<T>, b: seq<T>)
{
  |a| == |b|
}

function BitwiseElementAnd(a: bv32, b: bv32): bv32
{
  a & b
}

// </vc-helpers>

// <vc-spec>
method BitwiseAnd(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == (a[i] & b[i])
// </vc-spec>
// <vc-code>
{
  result := [];
  var index := 0;
  while index < |a|
    invariant |result| == index
    invariant index <= |a|
    invariant forall j :: 0 <= j < index ==> result[j] == (a[j] & b[j])
  {
    result := result + [a[index] & b[index]];
    index := index + 1;
  }
}
// </vc-code>
