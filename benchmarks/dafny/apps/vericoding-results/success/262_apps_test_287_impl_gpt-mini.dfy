predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 0 && k <= n
}

predicate ValidOutput(result: seq<int>, n: int, k: int)
{
    |result| == 2 && 
    result[0] >= 0 && 
    result[1] >= 0 && 
    result[0] <= result[1] &&
    result[0] <= n - k &&
    result[1] <= n - k
}

function MinGoodApartments(n: int, k: int): int
    requires ValidInput(n, k)
{
    if k == 0 || k == n then 0 else 1
}

function MaxGoodApartments(n: int, k: int): int
    requires ValidInput(n, k)
{
    if k == 0 || k == n then 0
    else if n - k < k * 2 then n - k
    else k * 2
}

// <vc-helpers>
lemma Min_bounds(n: int, k: int)
    requires ValidInput(n, k)
    ensures 0 <= MinGoodApartments(n, k) <= n - k
{
    if k == 0 || k == n {
        assert MinGoodApartments(n, k) == 0;
        // n - k >= 0 because k <= n
        assert n - k >= 0;
    } else {
        assert MinGoodApartments(n, k) == 1;
        // from k != n and k <= n we get k < n, hence n - k >= 1
        assert k < n;
        assert k + 1 <= n;
        assert n - k >= 1;
    }
}

lemma Max_bounds(n: int, k: int)
    requires ValidInput(n, k)
    ensures 0 <= MaxGoodApartments(n, k) <= n - k
{
    if k == 0 || k == n {
        assert MaxGoodApartments(n, k) == 0;
        assert n - k >= 0;
    } else {
        if n - k < k * 2 {
            assert MaxGoodApartments(n, k) == n - k;
        } else {
            assert MaxGoodApartments(n, k) == k * 2;
            // from !(n-k < 2*k) we have n-k >= 2*k
            assert n - k >= k * 2;
        }
    }
}

lemma Min_le_Max(n: int, k: int)
    requires ValidInput(n, k)
    ensures MinGoodApartments(n, k) <= MaxGoodApartments(n, k)
{
    if k == 0 || k == n {
        assert MinGoodApartments(n, k) == 0;
        assert MaxGoodApartments(n, k) == 0;
    } else {
        assert MinGoodApartments(n, k) == 1;
        if n - k < k * 2 {
            assert MaxGoodApartments(n, k) == n - k;
            // as before n - k >= 1 because k < n
            assert k < n;
            assert k + 1 <= n;
            assert n - k >= 1;
        } else {
            assert MaxGoodApartments(n, k) == k * 2;
            // k != 0 here, so k >= 1
            assert k != 0;
            assert k >= 1;
            assert k * 2 >= 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == MinGoodApartments(n, k)
    ensures result[1] == MaxGoodApartments(n, k)
// </vc-spec>
// <vc-code>
{
  var a := MinGoodApartments(n, k);
  var b := MaxGoodApartments(n, k);
  Min_bounds(n, k);
  Max_bounds(n, k);
  Min_le_Max(n, k);
  result := [a, b];
}
// </vc-code>

