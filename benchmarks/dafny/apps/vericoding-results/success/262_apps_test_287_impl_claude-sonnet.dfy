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
lemma ValidOutputProperties(n: int, k: int)
    requires ValidInput(n, k)
    ensures MinGoodApartments(n, k) >= 0
    ensures MaxGoodApartments(n, k) >= 0
    ensures MinGoodApartments(n, k) <= MaxGoodApartments(n, k)
    ensures MinGoodApartments(n, k) <= n - k
    ensures MaxGoodApartments(n, k) <= n - k
{
    if k == 0 || k == n {
        assert MinGoodApartments(n, k) == 0;
        assert MaxGoodApartments(n, k) == 0;
    } else {
        assert MinGoodApartments(n, k) == 1;
        if n - k < k * 2 {
            assert MaxGoodApartments(n, k) == n - k;
        } else {
            assert MaxGoodApartments(n, k) == k * 2;
            assert k * 2 <= n - k;
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
    ValidOutputProperties(n, k);
    result := [MinGoodApartments(n, k), MaxGoodApartments(n, k)];
}
// </vc-code>

