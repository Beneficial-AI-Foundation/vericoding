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
lemma sorted_pos(a: int, b: int, c: int)
    ensures pos1(a,b,c) <= pos2(a,b,c)
    ensures pos2(a,b,c) <= pos3(a,b,c)
{
}

lemma PositiveDifference(val: int, diff: int)
    ensures (if val > diff then val - diff else 0) >= 0
{
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
    var p1 := pos1(a, b, c);
    var p2 := pos2(a, b, c);
    var p3 := pos3(a, b, c);

    var diff1 := p2 - p1;
    var diff2 := p3 - p2;

    var term1 := if d > diff1 then d - diff1 else 0;
    var term2 := if d > diff2 then d - diff2 else 0;
    
    result := term1 + term2;
}
// </vc-code>

