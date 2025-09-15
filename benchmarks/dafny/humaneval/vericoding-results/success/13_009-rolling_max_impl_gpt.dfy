// <vc-preamble>
datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): declared pure functions (no 'method') and added specifications for max to aid verification */
function max(a: int, b: int): int
  ensures a <= max(a, b)
  ensures b <= max(a, b)
  ensures max(a, b) == a || max(a, b) == b
{
  if a < b then b else a
}

/* helper modified by LLM (iteration 2): recursive prefix maximums function with specifications matching rolling_max ensures */
function prefixMaxes(s: seq<int>): seq<int>
  decreases |s|
  ensures |prefixMaxes(s)| == |s|
  ensures forall i: int :: 0 <= i && i < |s| ==> s[i] <= prefixMaxes(s)[i]
  ensures forall i: int :: 0 <= i && i + 1 < |s| ==> prefixMaxes(s)[i] <= prefixMaxes(s)[i + 1]
{
  if |s| == 0 then []
  else if |s| == 1 then [s[0]]
  else prefixMaxes(s[..|s|-1]) + [max(prefixMaxes(s[..|s|-1])[|s|-2], s[|s|-1])]
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)

    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute result using prefixMaxes */
  result := prefixMaxes(numbers);
}
// </vc-code>
