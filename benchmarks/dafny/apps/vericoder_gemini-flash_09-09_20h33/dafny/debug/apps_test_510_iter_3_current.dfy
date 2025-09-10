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
function min(a: int, b: int): int {
    if a <= b then a else b
}

function max(a: int, b: int): int {
    if a >= b then a else b
}

lemma pos1_is_min(a: int, b: int, c: int)
    ensures pos1(a,b,c) == min(min(a,b),c)
{
    if a <= b && a <= c {
        assert pos1(a,b,c) == a;
        assert a == min(a,b) by { assert a <= b; }
        assert a == min(min(a,b),c) by { assert min(a,b) == a; assert a <= c; }
    } else if b <= a && b <= c {
        assert pos1(a,b,c) == b;
        assert b == min(a,b) by { assert b <= a; }
        assert b == min(min(a,b),c) by { assert min(a,b) == b; assert b <= c; }
    } else { // c is the minimum
        assert pos1(a,b,c) == c;
        if (a <= b) { // min(a,b) is a
            assert min(min(a,b),c) == min(a,c);
            assert c <= a;
        } else { // min(a,b) is b
            assert min(min(a,b),c) == min(b,c);
            assert c <= b;
        }
    }
}

lemma pos2_is_second_min(a: int, b: int, c: int)
    ensures pos2(a, b, c) == (if a <= b && a <= c then min(b, c)
                             else if b <= a && b <= c then min(a, c)
                             else min(a, b))
{
}

lemma pos3_is_max(a: int, b: int, c: int)
    ensures pos3(a, b, c) == max(max(a, b), c)
{
}

lemma sorted_pos_values(a: int, b: int, c: int)
    ensures pos1(a, b, c) <= pos2(a, b, c)
    ensures pos2(a, b, c) <= pos3(a, b, c)
{
    if a <= b && a <= c { // Case 1: a is min
        assert pos1(a,b,c) == a;
        if b <= c { // implies a <= b <= c
            assert pos2(a,b,c) == b;
            assert pos3(a,b,c) == c;
        } else { // implies a <= c <= b
            assert pos2(a,b,c) == c;
            assert pos3(a,b,c) == b;
        }
    } else if b <= a && b <= c { // Case 2: b is min
        assert pos1(a,b,c) == b;
        if a <= c { // implies b <= a <= c
            assert pos2(a,b,c) == a;
            assert pos3(a,b,c) == c;
        } else { // implies b <= c <= a
            assert pos2(a,b,c) == c;
            assert pos3(a,b,c) == a;
        }
    } else { // Case 3: c is min, implies c <= a && c <= b
        assert pos1(a,b,c) == c;
        if a <= b { // implies c <= a <= b
            assert pos2(a,b,c) == a;
            assert pos3(a,b,c) == b;
        } else { // implies c <= b <= a
            assert pos2(a,b,c) == b;
            assert pos3(a,b,c) == a;
        }
    }
}

lemma calculate_terms(d: int, p1: int, p2: int, p3: int)
    returns (term1: int, term2: int)
    requires p1 <= p2 <= p3
    ensures term1 == (if d > (p2 - p1) then d - (p2 - p1) else 0)
    ensures term2 == (if d > (p3 - p2) then d - (p3 - p2) else 0)
{}
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
    sorted_pos_values(a, b, c);

    var val1 := pos1(a, b, c);
    var val2 := pos2(a, b, c);
    var val3 := pos3(a, b, c);

    var diff1 := val2 - val1;
    var diff2 := val3 - val2;

    var term1 := 0;
    if d > diff1 {
        term1 := d - diff1;
    }

    var term2 := 0;
    if d > diff2 {
        term2 := d - diff2;
    }

    result := term1 + term2;
}
// </vc-code>

