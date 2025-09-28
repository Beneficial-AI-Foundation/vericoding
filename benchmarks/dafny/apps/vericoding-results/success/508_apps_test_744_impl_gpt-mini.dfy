function count_sf_flights(s: string): int
{
    if |s| <= 1 then 0
    else (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1])
}

function count_fs_flights(s: string): int
{
    if |s| <= 1 then 0
    else (if s[|s|-1] == 'S' && s[|s|-2] != 'S' then 1 else 0) + count_fs_flights(s[..|s|-1])
}

// <vc-helpers>
lemma count_sf_cons(s: string, i: int)
  requires 1 <= i < |s|
  ensures count_sf_flights(s[..i+1]) == count_sf_flights(s[..i]) + (if s[i] == 'F' && s[i-1] != 'F' then 1 else 0)
{
  var t := s[..i+1];
  // relationships between t and s
  assert |t| == i+1;
  assert t[|t|-1] == s[i];
  assert t[|t|-2] == s[i-1];
  assert t[..|t|-1] == s[..i];
  // unfold the definition of count_sf_flights on t
  assert count_sf_flights(t) == (if t[|t|-1] == 'F' && t[|t|-2] != 'F' then 1 else 0) + count_sf_flights(t[..|t|-1]);
  // substitute back to s
  assert (if t[|t|-1] == 'F' && t[|t|-2] != 'F' then 1 else 0) + count_sf_flights(t[..|t|-1])
         == (if s[i] == 'F' && s[i-1] != 'F' then 1 else 0) + count_sf_flights(s[..i]);
  // conclude
  assert count_sf_flights(s[..i+1]) == count_sf_flights(s[..i]) + (if s[i] == 'F' && s[i-1] != 'F' then 1 else 0);
}

lemma count_fs_cons(s: string, i: int)
  requires 1 <= i < |s|
  ensures count_fs_flights(s[..i+1]) == count_fs_flights(s[..i]) + (if s[i] == 'S' && s[i-1] != 'S' then 1 else 0)
{
  var t := s[..i+1];
  assert |t| == i+1;
  assert t[|t|-1] == s[i];
  assert t[|t|-2] == s[i-1];
  assert t[..|t|-1] == s[..i];
  assert count_fs_flights(t) == (if t[|t|-1] == 'S' && t[|t|-2] != 'S' then 1 else 0) + count_fs_flights(t[..|t|-1]);
  assert (if t[|t|-1] == 'S' && t[|t|-2] != 'S' then 1 else 0) + count_fs_flights(t[..|t|-1])
         == (if s[i] == 'S' && s[i-1] != 'S' then 1 else 0) + count_fs_flights(s[..i]);
  assert count_fs_flights(s[..i+1]) == count_fs_flights(s[..i]) + (if s[i] == 'S' && s[i-1] != 'S' then 1 else 0);
}

lemma count_sf_full(s: string)
  ensures count_sf_flights(s[..|s|]) == count_sf_flights(s)
  decreases |s|
{
  if |s| <= 1 {
    // both sides are 0 by definition
  } else {
    // unfold both definitions and relate them
    assert count_sf_flights(s) == (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1]);
    var t := s[..|s|];
    assert |t| == |s|;
    assert t[|t|-1] == s[|s|-1];
    assert t[|t|-2] == s[|s|-2];
    assert t[..|t|-1] == s[..|s|-1];
    assert count_sf_flights(t) == (if t[|t|-1] == 'F' && t[|t|-2] != 'F' then 1 else 0) + count_sf_flights(t[..|t|-1]);
    // substitute equalities to get same RHS
    assert count_sf_flights(t) == (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1]);
    // apply induction on the prefix
    count_sf_full(s[..|s|-1]);
    // after induction, the recursive parts are equal, so full values equal
    assert count_sf_flights(s[..|s|-1]) == count_sf_flights(s[..|s|-1]);
    assert count_sf_flights(t) == (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1]);
    assert count_sf_flights(s) == (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1]);
    assert count_sf_flights(t) == count_sf_flights(s);
  }
}

lemma count_fs_full(s: string)
  ensures count_fs_flights(s[..|s|]) == count_fs_flights(s)
  decreases |s|
{
  if |s| <= 1 {
    // both sides are 0 by definition
  } else {
    assert count_fs_flights(s) == (if s[|s|-1] == 'S' && s[|s|-2] != 'S' then 1 else 0) + count_fs_flights(s[..|s|-1]);
    var t := s[..|s|];
    assert |t| == |s|;
    assert t[|t|-1] == s[|s|-1];
    assert t[|t|-2] == s[|s|-2];
    assert t[..|t|-1] == s[..|s|-1];
    assert count_fs_flights(t) == (if t[|t|-1] == 'S' && t[|t|-2] != 'S' then 1 else 0) + count_fs_flights(t[..|t|-1]);
    assert count_fs_flights(t) == (if s[|s|-1] == 'S' && s[|s|-2] != 'S' then 1 else 0) + count_fs_flights(s[..|s|-1]);
    count_fs_full(s[..|s|-1]);
    assert count_fs_flights(t) == count_fs_flights(s);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires n >= 2
    requires |s| == n
    requires forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'F'
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> count_sf_flights(s) > count_fs_flights(s)
// </vc-spec>
// <vc-code>
{
  var sf := 0;
  var fs := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sf == count_sf_flights(s[..i])
    invariant fs == count_fs_flights(s[..i])
  {
    if i == 0 {
      i := i + 1;
      continue;
    }
    // remember previous counts (they equal counts on s[..i] by invariant)
    var prev_sf := sf;
    var prev_fs := fs;

    if s[i] == 'F' && s[i-1] != 'F' {
      sf := sf + 1;
    }
    if s[i] == 'S' && s[i-1] != 'S' {
      fs := fs + 1;
    }

    if 1 <= i < n {
      // use lemmas to relate counts on s[..i+1] to s[..i]
      count_sf_cons(s, i);
      count_fs_cons(s, i);

      // prev_* == count_*_flights(s[..i]) by invariant when prev_* were assigned
      assert prev_sf == count_sf_flights(s[..i]);
      assert prev_fs == count_fs_flights(s[..i]);

      // sf/fs were updated from prev_* by exactly the conditional increments
      assert sf == prev_sf + (if s[i] == 'F' && s[i-1] != 'F' then 1 else 0);
      assert fs == prev_fs + (if s[i] == 'S' && s[i-1] != 'S' then 1 else 0);

      // combine with lemmas to obtain counts on s[..i+1]
      assert sf == count_sf_flights(s[..i+1]);
      assert fs == count_fs_flights(s[..i+1]);
    }

    i := i + 1;
  }
  // now i == n and invariants give sf and fs equal to counts on full string slice s[..n]
  // relate count on s[..n] to count on s (note n == |s|)
  count_sf_full(s);
  count_fs_full(s);

  if sf > fs {
    result := "YES";
  } else {
    result := "NO";
  }
  assert sf == count_sf_flights(s);
  assert fs == count_fs_flights(s);
  if sf > fs {
    assert result == "YES";
  } else {
    assert result == "NO";
  }
}
// </vc-code>

