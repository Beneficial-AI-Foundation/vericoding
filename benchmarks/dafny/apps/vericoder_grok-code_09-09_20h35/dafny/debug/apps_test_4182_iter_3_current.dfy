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

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>) returns (result: string)
    requires ValidInput(n, m, x, y, xx, yy)
    ensures result == "No War" || result == "War"
    ensures result == "No War" <==> AgreementPossible(n, m, x, y, xx, yy)
// </vc-spec>
// <vc-code>
{
  var combined_x := xx + [x];
  var max_val := combined_x[0];
  var i := 1;
  while i < |combined_x|
    invariant 0 <= i <= |combined_x|
    invariant forall k :: 0 <= k < i ==> combined_x[k] <= max_val
    invariant max_val in combined_x
  {
    if combined_x[i] > max_val {
      max_val := combined_x[i];
    }
    i := i + 1;
  }
  var combined_y := yy + [y];
  var min_val := combined_y[0];
  i := 1;
  while i < |combined_y|
    invariant 0 <= i <= |combined_y|
    invariant forall k :: 0 <= k < i ==> combined_y[k] >= min_val
    invariant min_val in combined_y
  {
    if combined_y[i] < min_val {
      min_val := combined_y[i];
    }
    i := i + 1;
  }
  if max_val < min_val {
    result := "No War";
  } else {
    result := "War";
  }
}
// </vc-code>

