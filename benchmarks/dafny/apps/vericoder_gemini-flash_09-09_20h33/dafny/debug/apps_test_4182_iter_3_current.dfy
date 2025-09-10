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
function Max(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0] else Max(s[..|s|-1]) max s[|s|-1]
}

function Min(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0] else Min(s[..|s|-1]) min s[|s|-1]
}

lemma lemma_max_in_seq(s: seq<int>)
  requires |s| > 0
  ensures (exists max_val :: max_val == Max(s) && max_val in s)
  decreases |s|
{
  if |s| == 1 {
    // nothing to do, Base case
  } else {
    lemma_max_in_seq(s[..|s|-1]);
    if Max(s[..|s|-1]) < s[|s|-1] {
        assert Max(s) == s[|s|-1];
        assert Max(s) in s;
    } else {
        assert Max(s) == Max(s[..|s|-1]);
        assert Max(s) in s[..|s|-1];
        assert Max(s) in s;
    }
  }
}

lemma lemma_min_in_seq(s: seq<int>)
  requires |s| > 0
  ensures (exists min_val :: min_val == Min(s) && min_val in s)
  decreases |s|
{
  if |s| == 1 {
    // nothing to do, Base case
  } else {
    lemma_min_in_seq(s[..|s|-1]);
    if Min(s[..|s|-1]) > s[|s|-1] {
        assert Min(s) == s[|s|-1];
        assert Min(s) in s;
    } else {
        assert Min(s) == Min(s[..|s|-1]);
        assert Min(s) in s[..|s|-1];
        assert Min(s) in s;
    }
  }
}

lemma lemma_max_is_max_of_itself_and_elements(s: seq<int>)
  requires |s| > 0
  ensures forall v :: v in s ==> v <= Max(s)
  decreases |s|
{
  if |s| == 1 {
    assert true;
  } else {
    lemma_max_is_max_of_itself_and_elements(s[..|s|-1]);
    ghost var current_max := Max(s[..|s|-1]);
    assert forall v :: v in s[..|s|-1] ==> v <= current_max;
    if s[|s|-1] > current_max {
      assert Max(s) == s[|s|-1];
    } else {
      assert Max(s) == current_max;
    }
  }
}

lemma lemma_min_is_min_of_itself_and_elements(s: seq<int>)
  requires |s| > 0
  ensures forall v :: v in s ==> v >= Min(s)
  decreases |s|
{
  if |s| == 1 {
    assert true;
  } else {
    lemma_min_is_min_of_itself_and_elements(s[..|s|-1]);
    ghost var current_min := Min(s[..|s|-1]);
    assert forall v :: v in s[..|s|-1] ==> v >= current_min;
    if s[|s|-1] < current_min {
      assert Min(s) == s[|s|-1];
    } else {
      assert Min(s) == current_min;
    }
  }
}
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
    var combined_y := yy + [y];

    lemma_max_in_seq(combined_x);
    lemma_max_is_max_of_itself_and_elements(combined_x);
    lemma_min_in_seq(combined_y);
    lemma_min_is_min_of_itself_and_elements(combined_y);

    var max_x_all := Max(combined_x);
    var min_y_all := Min(combined_y);

    if max_x_all < min_y_all then
        result := "No War";
    else
        result := "War";
    
    calc {
        AgreementPossible(n, m, x, y, xx, yy);
        (exists max_val :: max_val in combined_x && 
                         (forall v :: v in combined_x ==> v <= max_val) &&
         exists min_val :: min_val in combined_y && 
                         (forall v :: v in combined_y ==> v >= min_val) &&
                         max_val < min_val);
        {
          assert max_x_all in combined_x;
          assert forall v :: v in combined_x ==> v <= max_x_all;
          assert min_y_all in combined_y;
          assert forall v :: v in combined_y ==> v >= min_y_all;
        }
        (max_x_all in combined_x && 
         (forall v :: v in combined_x ==> v <= max_x_all) &&
         min_y_all in combined_y && 
         (forall v :: v in combined_y ==> v >= min_y_all) &&
         max_x_all < min_y_all);
        (max_x_all < min_y_all);
    }
}
// </vc-code>

