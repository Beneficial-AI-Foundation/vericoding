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
lemma pos_ordering(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= pos2(a, b, c) <= pos3(a, b, c)
{
    // This lemma helps verify that pos1 <= pos2 <= pos3
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
    var med := pos2(a, b, c);
    var max := pos3(a, b, c);
    
    pos_ordering(a, b, c);
    
    var gap1 := med - min;
    var gap2 := max - med;
    
    var excess1 := if d > gap1 then d - gap1 else 0;
    var excess2 := if d > gap2 then d - gap2 else 0;
    
    result := excess1 + excess2;
}
// </vc-code>

