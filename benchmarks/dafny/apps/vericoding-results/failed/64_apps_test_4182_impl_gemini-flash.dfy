// <vc-preamble>
predicate ValidInput(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
{
    |xx| == n && |yy| == m && n >= 1 && m >= 1 && x < y
}

predicate AgreementPossible(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
    requires ValidInput(n, m, x, y, xx, yy)
{
    var combined_x := xx + [x];
    var combined_y := yy + [y];
    (exists max_val :: max_val in combined_x && 
                     (forall v :: v in combined_x ==> v <= max_val) &&
     exists min_val :: min_val in combined_y && 
                     (forall v :: v in combined_y ==> v >= min_val) &&
                     max_val < min_val)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed `GetMax` and `GetMin` base cases using `s[0]` */
function GetMax(s: seq<int>): int
  requires s != []
  ensures forall v :: v in s ==> v <= GetMax(s)
  ensures exists v :: v in s && v == GetMax(s)
{
  if |s| == 1 then s[0]
  else
    var max_of_rest := GetMax(s[1..]);
    if s[0] > max_of_rest then s[0]
    else max_of_rest
}

function GetMin(s: seq<int>): int
  requires s != []
  ensures forall v :: v in s ==> v >= GetMin(s)
  ensures exists v :: v in s && v == GetMin(s)
{
  if |s| == 1 then s[0]
  else
    var min_of_rest := GetMin(s[1..]);
    if s[0] < min_of_rest then s[0]
    else min_of_rest
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>) returns (result: string)
    requires ValidInput(n, m, x, y, xx, yy)
    ensures result == "No War" || result == "War"
    ensures result == "No War" <==> AgreementPossible(n, m, x, y, xx, yy)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): called helper functions directly for AgreementPossible check instead of relying on the combined sequence definition implicitly satisfying its requirements */
{
  var combined_x := xx + [x];
  var combined_y := yy + [y];

  // Check if AgreementPossible is true
  var max_val_xx := GetMax(combined_x);
  var min_val_yy := GetMin(combined_y);

  if max_val_xx < min_val_yy {
    result := "No War";
  } else {
    result := "War";
  }
}
// </vc-code>
