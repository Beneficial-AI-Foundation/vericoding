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
        // Base case
        assert MaxSeq(s) == s[0];
        assert s[0] in s;
        forall v | v in s {
            assert v <= s[0];
        }
    } else {
        var t := s[0];
        var rest := s[1..];
        MaxSeq_properties(rest);
        var m := MaxSeq(rest);
        // By definition of MaxSeq, MaxSeq(s) == (if t >= m then t else m)
        assert MaxSeq(s) == (if t >= m then t else m);
        if t >= m {
            // Max is head
            assert MaxSeq(s) == t;
            assert t in s;
            // Prove upper bound property
            forall v | v in s {
                if v == t {
                    assert v <= t;
                } else {
                    // then v in rest
                    assert v in rest;
                    assert v <= m; // from recursive property
                    assert m <= t;
                    assert v <= t;
                }
            }
        } else {
            // Max is from rest
            assert MaxSeq(s) == m;
            assert m in rest;
            assert m in s;
            // Prove upper bound property
            forall v | v in s {
                if v == t {
                    assert t <= m;
                } else {
                    assert v in rest;
                    assert v <= m; // from recursive property
                }
            }
        }
    }
}

lemma MinSeq_properties(s: seq<int>)
    requires |s| >= 1
    ensures MinSeq(s) in s
    ensures forall v :: v in s ==> v >= MinSeq(s)
{
    if |s| == 1 {
        // Base case
        assert MinSeq(s) == s[0];
        assert s[0] in s;
        forall v | v in s {
            assert v >= s[0];
        }
    } else {
        var t := s[0];
        var rest := s[1..];
        MinSeq_properties(rest);
        var m := MinSeq(rest);
        // By definition of MinSeq, MinSeq(s) == (if t <= m then t else m)
        assert MinSeq(s) == (if t <= m then t else m);
        if t <= m {
            // Min is head
            assert MinSeq(s) == t;
            assert t in s;
            // Prove lower bound property
            forall v | v in s {
                if v == t {
                    assert v >= t;
                } else {
                    // then v in rest
                    assert v in rest;
                    assert v >= m; // from recursive property
                    assert m >= t;
                    assert v >= t;
                }
            }
        } else {
            // Min is from rest
            assert MinSeq(s) == m;
            assert m in rest;
            assert m in s;
            // Prove lower bound property
            forall v | v in s {
                if v == t {
                    assert t >= m;
                } else {
                    assert v in rest;
                    assert v >= m; // from recursive property
                }
            }
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
    MinSeq_properties(cy);
    // -> : AgreementPossible ==> MaxSeq(cx) < MinSeq(cy)
    if AgreementPossible(n, m, x, y, xx, yy) {
        var maxv :| maxv in cx && (forall v :: v in cx ==> v <= maxv);
        var minv :| minv in cy && (forall v :: v in cy ==> v >= minv);
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

