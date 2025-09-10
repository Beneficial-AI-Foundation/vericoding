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
  if |s| == 1 then s[0] else (Max(s[..|s|-1]) max s[|s|-1])
}

function Min(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0] else (Min(s[..|s|-1]) min s[|s|-1])
}

lemma lemma_max_in_seq(s: seq<int>)
  requires |s| > 0
  ensures Max(s) in s
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
  ensures Min(s) in s
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
    ghost var current_max_prefix := Max(s[..|s|-1]);
    assert forall v :: v in s[..|s|-1] ==> v <= current_max_prefix;
    if s[|s|-1] > current_max_prefix {
      assert Max(s) == s[|s|-1];
      assert forall v :: v in s ==> v <= Max(s);
    } else {
      assert Max(s) == current_max_prefix;
      assert forall v :: v in s ==> v <= Max(s);
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
    ghost var current_min_prefix := Min(s[..|s|-1]);
    assert forall v :: v in s[..|s|-1] ==> v >= current_min_prefix;
    if s[|s|-1] < current_min_prefix {
      assert Min(s) == s[|s|-1];
      assert forall v :: v in s ==> v >= Min(s);
    } else {
      assert Min(s) == current_min_prefix;
      assert forall v :: v in s ==> v >= Min(s);
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

    // combined_x and combined_y are guaranteed to have at least one element because |xx| >= 1 and |yy| >= 1
    // (from ValidInput and definition of combined_x/y)
    // So the preconditions for Max and Min functions, and their lemmas, are met.
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
          assert max_x_all in combined_x; // from lemma_max_in_seq
          assert forall v :: v in combined_x ==> v <= max_x_all; // from lemma_max_is_max_of_itself_and_elements
          assert min_y_all in combined_y; // from lemma_min_in_seq
          assert forall v :: v in combined_y ==> v >= min_y_all; // from lemma_min_is_min_of_itself_and_elements
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

