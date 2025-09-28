// <vc-preamble>

predicate ValidInput(number: int, need: int, remaining: int)
{
    0 <= number <= 1000 && 0 <= need <= 1000 && 0 <= remaining <= 1000
}

function CanEat(need: int, remaining: int): int
{
    if need <= remaining then need else remaining
}

function TotalEaten(number: int, need: int, remaining: int): int
{
    number + CanEat(need, remaining)
}

function CarrotsLeft(need: int, remaining: int): int
{
    remaining - CanEat(need, remaining)
}

predicate ValidResult(result: seq<int>, number: int, need: int, remaining: int)
{
    |result| == 2 &&
    result[0] == TotalEaten(number, need, remaining) &&
    result[1] == CarrotsLeft(need, remaining) &&
    result[0] >= number &&
    result[1] >= 0 &&
    result[1] <= remaining
}
// </vc-preamble>

// <vc-helpers>

function TotalEatenValid(number: int, need: int, remaining: int): bool
{
    TotalEaten(number, need, remaining) >= number
}

function CarrotsLeftValid(need: int, remaining: int): bool
{
    var eaten := CanEat(need, remaining);
    remaining - eaten >= 0 && remaining - eaten <= remaining
}

lemma ValidResultLemma(number: int, need: int, remaining: int)
    requires ValidInput(number, need, remaining)
    ensures TotalEaten(number, need, remaining) >= number
    ensures var left := CarrotsLeft(need, remaining); left >= 0 && left <= remaining
{
    // Proof that total eaten >= number
    var eaten := CanEat(need, remaining);
    if need <= remaining {
        assert eaten == need;
        assert TotalEaten(number, need, remaining) == number + need;
        assert number + need >= number;
    } else {
        assert eaten == remaining;
        assert TotalEaten(number, need, remaining) == number + remaining;
        assert number + remaining >= number;
    }
    
    // Proof that carrots left is valid
    var carrots_left := remaining - eaten;
    assert carrots_left >= 0;
    assert carrots_left <= remaining;
    assert carrots_left == CarrotsLeft(need, remaining);
}

// </vc-helpers>

// <vc-spec>
method eat(number: int, need: int, remaining: int) returns (result: seq<int>)
    requires ValidInput(number, need, remaining)
    ensures ValidResult(result, number, need, remaining)
// </vc-spec>
// <vc-code>
{
    ValidResultLemma(number, need, remaining);
    var total := TotalEaten(number, need, remaining);
    var left := CarrotsLeft(need, remaining);
    result := [total, left];
    assert |result| == 2;
    assert result[0] == total;
    assert result[1] == left;
}
// </vc-code>
