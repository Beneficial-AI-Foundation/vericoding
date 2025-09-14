// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sequence comprehension syntax */
function Sort(s: seq<int>): seq<int>
  ensures multiset(Sort(s)) == multiset(s)
  ensures |Sort(s)| == |s|
  ensures forall i, j :: 0 <= i <= j < |Sort(s)| ==> Sort(s)[i] <= Sort(s)[j]
{
  if |s| < 2 then s
  else
    var pivot := s[0];
    var less := Sort([x | x <- s[1..] | x <= pivot]);
    var more := Sort([x | x <- s[1..] | x > pivot]);
    less + [pivot] + more
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)

    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): retained logic as error was in helper compilation */
  sorted := Sort(s);
  strange := seq(|s|, i =>
    if i % 2 == 0 then sorted[i/2]
    else sorted[|s| - (i - 1) / 2 - 1]
  );
}
// </vc-code>
