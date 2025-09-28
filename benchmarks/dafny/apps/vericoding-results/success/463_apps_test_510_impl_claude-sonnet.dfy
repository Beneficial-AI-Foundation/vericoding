function pos1(a: int, b: int, c: int): int
{
    if a <= b && a <= c then a
    else if b <= a && b <= c then b
    else c
}

function pos2(a: int, b: int, c: int): int
{
    if a <= b && a <= c then
        if b <= c then b else c
    else if b <= a && b <= c then
        if a <= c then a else c
    else
        if a <= b then a else b
}

function pos3(a: int, b: int, c: int): int
{
    if a <= b && a <= c then
        if b <= c then c else b
    else if b <= a && b <= c then
        if a <= c then c else a
    else
        if a <= b then b else a
}

// <vc-helpers>
lemma pos1_is_min(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= a && pos1(a, b, c) <= b && pos1(a, b, c) <= c
    ensures pos1(a, b, c) == a || pos1(a, b, c) == b || pos1(a, b, c) == c
{
}

lemma pos2_is_middle(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= pos2(a, b, c) <= pos3(a, b, c)
    ensures pos2(a, b, c) == a || pos2(a, b, c) == b || pos2(a, b, c) == c
{
}

lemma pos3_is_max(a: int, b: int, c: int)
    ensures pos3(a, b, c) >= a && pos3(a, b, c) >= b && pos3(a, b, c) >= c
    ensures pos3(a, b, c) == a || pos3(a, b, c) == b || pos3(a, b, c) == c
{
}

lemma ordering_lemma(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= pos2(a, b, c) <= pos3(a, b, c)
{
    pos1_is_min(a, b, c);
    pos2_is_middle(a, b, c);
    pos3_is_max(a, b, c);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires 1 <= a <= 1_000_000_000
    requires 1 <= b <= 1_000_000_000
    requires 1 <= c <= 1_000_000_000
    requires 1 <= d <= 1_000_000_000
    ensures result >= 0
    ensures result == (if d > (pos2(a, b, c) - pos1(a, b, c)) then d - (pos2(a, b, c) - pos1(a, b, c)) else 0) +
                     (if d > (pos3(a, b, c) - pos2(a, b, c)) then d - (pos3(a, b, c) - pos2(a, b, c)) else 0)
// </vc-spec>
// <vc-code>
{
    var min := pos1(a, b, c);
    var mid := pos2(a, b, c);
    var max := pos3(a, b, c);
    
    ordering_lemma(a, b, c);
    
    var diff1 := mid - min;
    var diff2 := max - mid;
    
    var term1 := if d > diff1 then d - diff1 else 0;
    var term2 := if d > diff2 then d - diff2 else 0;
    
    result := term1 + term2;
}
// </vc-code>

