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
function max(a: int, b: int): int { if a > b then a else b }
function seq_max(s: seq<int>): int
  requires |s| > 0
  ensures forall i : int :: 0 <= i < |s| ==> s[i] <= seq_max(s)
  ensures exists i : int :: 0 <= i < |s| && s[i] == seq_max(s)
{
  if |s| == 1 then
    s[0]
  else
    max(s[0], seq_max(s[1..]))
}
lemma RollingMaxLemma(numbers: seq<int>, result: seq<int>, k: int)
  requires |numbers| == |result|
  requires 0 <= k < |numbers|
  requires forall j : int :: 0 <= j <= k ==> result[j] == seq_max(numbers[0..j+1])
  ensures result[k] == seq_max(numbers[0..k+1])
{
}
/* helper modified by LLM (iteration 3): Fixed result reference in seq_max ensures clauses to use function name */
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)

    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Initialized result sequence properly before while loop */
  result := [];
  if |numbers| == 0 {
    return;
  }
  
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |result| == i
    invariant forall j : int :: 0 <= j < i ==> result[j] == seq_max(numbers[0..j+1])
    invariant forall j : int :: 0 <= j < i - 1 ==> result[j] <= result[j + 1]
  {
    var current_max := seq_max(numbers[0..i+1]);
    result := result + [current_max];
    i := i + 1;
  }
}
// </vc-code>
