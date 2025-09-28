// <vc-preamble>
predicate ValidInput(l: int, r: int)
{
    l < r && (r - l) % 2 == 1
}

function gcd(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if a >= 0 then a else -a
{
    if a == 0 then if b >= 0 then b else -b
    else gcd(b % a, a)
}

predicate PairHasGcdOne(pair: string, l: int, r: int)
{
    exists i, j :: l <= i <= r && l <= j <= r && i != j &&
        pair == int_to_string(i) + " " + int_to_string(j) &&
        (i != 0 || j != 0) && gcd(i, j) == 1
}

predicate ValidSolution(result: seq<string>, l: int, r: int)
{
    |result| >= 1 &&
    result[0] == "YES" &&
    |result| == 1 + (r - l + 1) / 2 &&
    (forall i :: 1 <= i < |result| ==> PairHasGcdOne(result[i], l, r))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper function `int_to_string` remains the same, as its previous version correctly identified the scope issue and fixed it. */
function int_to_string(i: int): string
{
    if i == 0 then "0"
    else if i < 0 then "-" + int_to_string(-i)
    else {
        var s := "";
        var n := i;
        while n > 0
            decreases n
        {
            s := (n % 10).ToString() + s;
            n := n / 10;
        }
        s
    }
}
// </vc-helpers>

// <vc-spec>
method solve(l: int, r: int) returns (result: seq<string>)
    requires ValidInput(l, r)
    ensures ValidSolution(result, l, r)
    ensures |result| >= 1
    ensures result[0] == "YES"
    ensures |result| == 1 + (r - l + 1) / 2
    ensures forall i :: 1 <= i < |result| ==> 
        (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
         result[i] == int_to_string(j) + " " + int_to_string(j + 1))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a syntax error where `result :=` was used instead of `result :=` inside the helper. Also, the variable `solution` is now returned as `result` based on the method signature. */
{
  var solution: seq<string> := ["YES"];
  var i := l;
  while i <= r - 1
    invariant l <= i <= r + 1
    invariant i % 2 == l % 2
    invariant |solution| == 1 + (i - l) / 2
    invariant forall k :: 1 <= k < |solution| ==> 
      (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && solution[k] == int_to_string(j) + " " + int_to_string(j + 1))
  {
    solution := solution + [int_to_string(i) + " " + int_to_string(i + 1)];
    i := i + 2;
  }
  return solution;
}
// </vc-code>
