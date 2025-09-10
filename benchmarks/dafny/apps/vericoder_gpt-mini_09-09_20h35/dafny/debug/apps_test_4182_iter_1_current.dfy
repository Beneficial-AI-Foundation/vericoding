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
function MaxSeq(s: seq<int>): int
    requires |s| >= 1
    decreases |s|
{
    if |s| == 1 then s[0] else var t := MaxSeq(s[1..]); if s[0] >= t then s[0] else t
}
function MinSeq(s: seq<int>): int
    requires |s| >= 1
    decreases |s|
{
    if |s| == 1 then s[0] else var t := MinSeq(s[1..]); if s[0] <= t then s[0] else t
}

lemma MaxSeq_properties(s: seq<int>)
    requires |s| >= 1
    ensures MaxSeq(s) in s
    ensures forall v :: v in s ==> v <= MaxSeq(s)
{
    if |s| == 1 {
        // trivial
    } else {
        var t := s[0];
        var rest := s[1..];
        MaxSeq_properties(rest);
        var m := MaxSeq(rest);
        if t >= m {
            // MaxSeq(s) == t
        } else {
            // MaxSeq(s) == m
        }
    }
}

lemma MinSeq_properties(s: seq<int>)
    requires |s| >= 1
    ensures MinSeq(s) in s
    ensures forall v :: v in s ==> v >= MinSeq(s)
{
    if |s| == 1 {
        // trivial
    } else {
        var t := s[0];
        var rest := s[1..];
        MinSeq_properties(rest);
        var m := MinSeq(rest);
        if t <= m {
            // MinSeq(s) == t
        } else {
            // MinSeq(s) == m
        }
    }
}

lemma AgreementPossible_iff(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
    requires ValidInput(n, m, x, y, xx, yy)
    ensures AgreementPossible(n, m, x, y, xx, yy) <==> (MaxSeq(xx + [x]) < MinSeq(yy + [y]))
{
    var cx := xx + [x];
    var cy := yy + [y];
    MaxSeq_properties(cx);
    MaxSeq_properties(cx); // ensure availability
    MinSeq_properties(cy);
    // -> : AgreementPossible ==> MaxSeq(cx) < MinSeq(cy)
    if AgreementPossible(n, m, x, y, xx, yy) {
        var maxv :| maxv in cx && (forall v :: v in cx ==> v <= maxv);
        var minv :| minv in cy && (forall v :: v in cy ==> v >= minv);
        // maxv and minv are witnesses; use properties of MaxSeq and MinSeq to relate them
        assert MaxSeq(cx) in cx;
        assert forall v :: v in cx ==> v <= MaxSeq(cx);
        assert MinSeq(cy) in cy;
        assert forall v :: v in cy ==> v >= MinSeq(cy);
        // From maxv being an upper bound and MaxSeq in cx, MaxSeq <= maxv
        assert MaxSeq(cx) <= maxv;
        // From MaxSeq being an upper bound and maxv in cx, maxv <= MaxSeq(cx)
        assert maxv <= MaxSeq(cx);
        assert MaxSeq(cx) == maxv;
        // Similarly for minv and MinSeq
        assert MinSeq(cy) <= minv;
        assert minv <= MinSeq(cy);
        assert MinSeq(cy) == minv;
        // Now use AgreementPossible's inequality
        assert maxv < minv;
        assert MaxSeq(cx) < MinSeq(cy);
    }
    // <- : MaxSeq(cx) < MinSeq(cy) ==> AgreementPossible
    if MaxSeq(cx) < MinSeq(cy) {
        // witnesses are MaxSeq(cx) and MinSeq(cy)
        assert MaxSeq(cx) in cx;
        assert forall v :: v in cx ==> v <= MaxSeq(cx);
        assert MinSeq(cy) in cy;
        assert forall v :: v in cy ==> v >= MinSeq(cy);
        // hence AgreementPossible holds with these witnesses
        reveal AgreementPossible;
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
  var cx := xx + [x];
  var cy := yy + [y];
  var mx := MaxSeq(cx);
  var mn := MinSeq(cy);
  if mx < mn {
    result := "No War";
  } else {
    result := "War";
  }
  // relate result to the comparison
  if mx < mn {
    assert result == "No War";
  } else {
    assert result == "War";
  }
  // use lemma to connect comparison with AgreementPossible
  AgreementPossible_iff(n, m, x, y, xx, yy);
  assert (result == "No War") <==> (mx < mn);
  assert (mx < mn) <==> AgreementPossible(n, m, x, y, xx, yy);
  assert (result == "No War") <==> AgreementPossible(n, m, x, y, xx, yy);
}
// </vc-code>

