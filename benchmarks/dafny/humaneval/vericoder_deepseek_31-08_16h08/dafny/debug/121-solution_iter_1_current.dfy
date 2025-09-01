

// <vc-helpers>
lemma EvenIndices(s: seq<int>, p: seq<bool>) returns (r: seq<bool>)
  requires |s| == |p|
  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == (p[i] && i % 2 == 0 && s[i] % 2 == 1)
{
  if |s| == 0 {
    r := [];
  } else {
    var tail_p := p[1..];
    var tail_s := s[1..];
    var tail_r := EvenIndices(tail_s, tail_p);
    if p[0] && 0 % 2 == 0 && s[0] % 2 == 1 {
      r := [true] + tail_r;
    } else {
      r := [false] + tail_r;
    }
  }
}

lemma SumEvenIndicesLemma(s: seq<int>, p: seq<bool>) returns (total: int)
  requires |s| == |p|
  ensures total == sum(s, EvenIndices(s, p))
{
  if |s| == 0 {
    total := 0;
  } else {
    var tail_p := p[1..];
    var tail_s := s[1..];
    var tail_total := SumEvenIndicesLemma(tail_s, tail_p);
    if p[0] && 0 % 2 == 0 && s[0] % 2 == 1 {
      total := s[0] + tail_total;
    } else {
      total := tail_total;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)
  // post-conditions-start
  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |numbers|;
  var predicate := seq(n, i requires 0 <= i < n => i % 2 == 0 && numbers[i] % 2 == 1);
  s := SumEvenIndicesLemma(numbers, predicate);
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end