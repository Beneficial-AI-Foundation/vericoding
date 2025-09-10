predicate ValidInput(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int)
{
    y1 < y2 < y_w &&
    y_b + r < y_w &&
    2 * r < y2 - y1 &&
    x_b > 0 && y_b > 0 && r > 0 &&
    2 * (y_w - r) - y1 - y_b - r != 0
}

function ComputeW(y_w: int, r: int): int
{
    y_w - r
}

function ComputeNewY1(y_w: int, r: int, y1: int, y_b: int): int
{
    2 * (y_w - r) - y1 - y_b - r
}

function ComputeNewY2(y_w: int, r: int, y2: int, y_b: int): int
{
    2 * (y_w - r) - y2 - y_b
}

function ComputeLeftSide(x_b: int, new_y1: int, new_y2: int): int
{
    x_b * x_b * (new_y2 - new_y1) * (new_y2 - new_y1)
}

function ComputeRightSide(x_b: int, new_y1: int, r: int): int
{
    (new_y1 * new_y1 + x_b * x_b) * r * r
}

predicate IsImpossible(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int)
    requires ValidInput(y1, y2, y_w, x_b, y_b, r)
{
    var w := ComputeW(y_w, r);
    var new_y1 := ComputeNewY1(y_w, r, y1, y_b);
    var new_y2 := ComputeNewY2(y_w, r, y2, y_b);
    var left_side := ComputeLeftSide(x_b, new_y1, new_y2);
    var right_side := ComputeRightSide(x_b, new_y1, r);
    left_side <= right_side
}

function ComputeSolution(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int): real
    requires ValidInput(y1, y2, y_w, x_b, y_b, r)
    requires !IsImpossible(y1, y2, y_w, x_b, y_b, r)
{
    var w := ComputeW(y_w, r);
    var new_y1 := ComputeNewY1(y_w, r, y1, y_b);
    (x_b as real) * ((new_y1 + y_b - w) as real) / (new_y1 as real)
}

// <vc-helpers>
lemma ValidInputProperty(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int)
    requires ValidInput(y1, y2, y_w, x_b, y_b, r)
    ensures var w := ComputeW(y_w, r);
            var new_y1 := ComputeNewY1(y_w, r, y1, y_b);
            var new_y2 := ComputeNewY2(y_w, r, y2, y_b);
            new_y1 > 0 &&
            new_y1 + y_b - w > 0 &&
            new_y2 - new_y1 < 0
{
    var w := ComputeW(y_w, r);
    assert w == y_w - r;
    var new_y1 := ComputeNewY1(y_w, r, y1, y_b);
    var new_y2 := ComputeNewY2(y_w, r, y2, y_b);

    calc {
        new_y1;
        2*(y_w - r) - y1 - y_b - r;
        2*y_w - 2*r - y1 - y_b - r;
        2*y_w - 3*r - y1 - y_b;
        >   { assert y_b < y_w - r; }
            2*y_w - 3*r - y1 - (y_w - r);
        =   2*y_w - 3*r - y1 - y_w + r;
        =   y_w - 2*r - y1;
        >   { assert y_w > y1 + 2*r; }
            0;
    }

    calc {
        new_y1 + y_b - w;
        2*(y_w - r) - y1 - y_b - r + y_b - (y_w - r);
        2*y_w - 2*r - y1 - r - y_w + r;
        y_w - y1 - 2*r;
        >   { assert y_w > y1 + 2*r; }
            0;
    }

    calc {
        new_y2 - new_y1;
        2*(y_w - r) - y2 - y_b - (2*(y_w - r) - y1 - y_b - r);
        - y2 - y_b + y1 + y_b + r;
        y1 - y2 + r;
        <   { assert 2*r < y2 - y1; }
            0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) returns (result: real)
    requires ValidInput(y1, y2, y_w, x_b, y_b, r)
    ensures IsImpossible(y1, y2, y_w, x_b, y_b, r) ==> result == -1.0
    ensures !IsImpossible(y1, y2, y_w, x_b, y_b, r) ==> result == ComputeSolution(y1, y2, y_w, x_b, y_b, r)
// </vc-spec>
// <vc-code>
{
    ValidInputProperty(y1, y2, y_w, x_b, y_b, r);
    if IsImpossible(y1, y2, y_w, x_b, y_b, r) then
        return -1.0;
    else
        return ComputeSolution(y1, y2, y_w, x_b, y_b, r);
}
// </vc-code>

