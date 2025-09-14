predicate ValidInput(n: int, pos: int, l: int, r: int)
{
    1 <= n <= 100 && 1 <= pos <= n && 1 <= l <= r <= n
}

predicate NoTabsToClose(l: int, r: int, n: int)
{
    l == 1 && r == n
}

predicate OnlyCloseRight(l: int, r: int, n: int)
{
    l == 1 && r < n
}

predicate OnlyCloseLeft(l: int, r: int, n: int)
{
    l > 1 && r == n
}

predicate CloseBothSides(l: int, r: int, n: int)
{
    l > 1 && r < n
}

// <vc-helpers>
function abs(x: int): int
{
  if x >= 0 then x else -x
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, pos: int, l: int, r: int) returns (result: int)
    requires ValidInput(n, pos, l, r)
    ensures result >= 0
    ensures NoTabsToClose(l, r, n) ==> result == 0
    ensures OnlyCloseRight(l, r, n) ==> result == abs(pos - r) + 1
    ensures OnlyCloseLeft(l, r, n) ==> result == abs(pos - l) + 1
    ensures CloseBothSides(l, r, n) && l <= pos <= r && pos - l < r - pos ==> result == (pos - l) + 1 + (r - l) + 1
    ensures CloseBothSides(l, r, n) && l <= pos <= r && pos - l >= r - pos ==> result == (r - pos) + 1 + (r - l) + 1
    ensures CloseBothSides(l, r, n) && pos > r ==> result == (pos - r) + 1 + (r - l) + 1
    ensures CloseBothSides(l, r, n) && pos < l ==> result == (l - pos) + 1 + (r - l) + 1
    ensures result <= 2 * n
// </vc-spec>
// <vc-code>
{
  if l == 1 && r == n {
    result := 0;
  } else if l == 1 && r < n {
    result := abs(pos - r) + 1;
    if pos >= r {
      assert abs(pos - r) == pos - r;
      assert pos <= n;
      assert r >= 1;
      assert pos - r <= n - 1;
    } else {
      assert abs(pos - r) == r - pos;
      assert r <= n;
      assert pos >= 1;
      assert r - pos <= n - 1;
    }
    assert abs(pos - r) + 1 <= (n - 1) + 1;
    assert (n - 1) + 1 <= 2 * n;
  } else if l > 1 && r == n {
    result := abs(pos - l) + 1;
    if pos >= l {
      assert abs(pos - l) == pos - l;
      assert pos <= n;
      assert l >= 1;
      assert pos - l <= n - 1;
    } else {
      assert abs(pos - l) == l - pos;
      assert l <= n;
      assert pos >= 1;
      assert l - pos <= n - 1;
    }
    assert abs(pos - l) + 1 <= (n - 1) + 1;
    assert (n - 1) + 1 <= 2 * n;
  } else {
    if pos < l {
      result := (l - pos) + 1 + (r - l) + 1;
      assert l <= n;
      assert pos >= 1;
      assert l - pos <= n - 1;
      assert r <= n;
      assert l >= 1;
      assert r - l <= n - 1;
      assert result <= (n - 1) + 1 + (n - 1) + 1;
      assert (n - 1) + 1 + (n - 1) + 1 == 2 * n;
    } else if pos > r {
      result := (pos - r) + 1 + (r - l) + 1;
      assert pos <= n;
      assert r >= 1;
      assert pos - r <= n - 1;
      assert r <= n;
      assert l >= 1;
      assert r - l <= n - 1;
      assert result <= (n - 1) + 1 + (n - 1) + 1;
      assert (n - 1) + 1 + (n - 1) + 1 == 2 * n;
    } else {
      assert l <= pos <= r;
      if pos - l < r - pos {
        result := (pos - l) + 1 + (r - l) + 1;
        assert pos >= l;
        assert pos <= r;
        assert pos - l <= r - l;
        assert r <= n;
        assert l >= 1;
        assert r - l <= n - 1;
        assert result <= (r - l) + 1 + (r - l) + 1;
        assert (r - l) + 1 + (r - l) + 1 <= (n - 1) + 1 + (n - 1) + 1;
        assert (n - 1) + 1 + (n - 1) + 1 == 2 * n;
      } else {
        result := (r - pos) + 1 + (r - l) + 1;
        assert pos >= l;
        assert pos <= r;
        assert r - pos <= r - l;
        assert r <= n;
        assert l >= 1;
        assert r - l <= n - 1;
        assert result <= (r - l) + 1 + (r - l) + 1;
        assert (r - l) + 1 + (r - l) + 1 <= (n - 1) + 1 + (n - 1) + 1;
        assert (n - 1) + 1 + (n - 1) + 1 == 2 * n;
      }
    }
  }
}
// </vc-code>

