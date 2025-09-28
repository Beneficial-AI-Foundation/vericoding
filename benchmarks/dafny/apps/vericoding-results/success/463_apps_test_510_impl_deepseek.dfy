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
lemma LemmaMinProperties(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= a
    ensures pos1(a, b, c) <= b
    ensures pos1(a, b, c) <= c
{
}

lemma LemmaMidProperties(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= pos2(a, b, c) <= pos3(a, b, c)
{
}

lemma LemmaDifferenceProperties(a: int, b: int, c: int)
    ensures pos2(a, b, c) - pos1(a, b, c) >= 0
    ensures pos3(a, b, c) - pos2(a, b, c) >= 0
{
    LemmaMinProperties(a, b, c);
    LemmaMidProperties(a, b, c);
}

lemma LemmaSolutionProperties(a: int, b: int, c: int, d: int)
    ensures (if d > (pos2(a, b, c) - pos1(a, b, c)) then d - (pos2(a, b, c) - pos1(a, b, c)) else 0) >= 0
    ensures (if d > (pos3(a, b, c) - pos2(a, b, c)) then d - (pos3(a, b, c) - pos2(a, b, c)) else 0) >= 0
{
    LemmaDifferenceProperties(a, b, c);
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
    LemmaDifferenceProperties(a, b, c);
    var diff1 := pos2(a, b, c) - pos1(a, b, c);
    var diff2 := pos3(a, b, c) - pos2(a, b, c);
    
    var part1 := if d > diff1 then d - diff1 else 0;
    var part2 := if d > diff2 then d - diff2 else 0;
    
    result := part1 + part2;
}
// </vc-code>

