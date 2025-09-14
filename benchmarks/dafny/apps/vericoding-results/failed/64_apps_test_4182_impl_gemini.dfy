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

// <vc-helpers>
lemma NotAP(combined_x: seq<int>, combined_y: seq<int>, my_max: int, my_min: int)
  requires |combined_x| > 0 && |combined_y| > 0
  requires my_max in combined_x
  requires forall v :: v in combined_x ==> v <= my_max
  requires
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>) returns (result: string)
    requires ValidInput(n, m, x, y, xx, yy)
    ensures result == "No War" || result == "War"
    ensures result == "No War" <==> AgreementPossible(n, m, x, y, xx, yy)
// </vc-spec>
// <vc-code>
lemma NotAP(combined_x: seq<int>, combined_y: seq<int>, my_max: int, my_min: int)
  requires |combined_x| > 0 && |combined_y| > 0
  requires my_max in combined_x
  requires forall v :: v in combined_x ==> v <= my_max
  requires
// </vc-code>

