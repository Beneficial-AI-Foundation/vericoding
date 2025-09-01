

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    res := false;
    if |s| < 4 {
        return;
    }
    var x := 0;
    while x < |s| - 3
        invariant 0 <= x <= |s| - 3
        invariant forall x', y', z', w' :: 0 <= x' < y' < z' < w' < x ==> !(s[x'] == 0 && s[y'] == 0 && s[z'] == 1 && s[w'] == 1)
        invariant res == (exists x_0, y_0, z_0, w_0 :: 0 <= x_0 < y_0 < z_0 < w_0 < x && s[x_0] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1)
    {
        if s[x] == 0 {
            var y := x + 1;
            while y < |s| - 2
                invariant x + 1 <= y <= |s| - 2
                invariant forall y', z', w' :: x < y' < z' < w' < y ==> !(s[x] == 0 && s[y'] == 0 && s[z'] == 1 && s[w'] == 1)
                invariant res == (exists x_0, y_0, z_0, w_0 :: 0 <= x_0 < y_0 < z_0 < w_0 < x && s[x_0] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1) ||
                                (exists y_0, z_0, w_0 :: x < y_0 < z_0 < w_0 < y && s[x] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1)
            {
                if s[y] == 0 {
                    var z := y + 1;
                    while z < |s| - 1
                        invariant y + 1 <= z <= |s| - 1
                        invariant forall z', w' :: y < z' < w' < z ==> !(s[x] == 0 && s[y] == 0 && s[z'] == 1 && s[w'] == 1)
                        invariant res == (exists x_0, y_0, z_0, w_0 :: 0 <= x_0 < y_0 < z_0 < w_0 < x && s[x_0] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1) ||
                                        (exists y_0, z_0, w_0 :: x < y_0 < z_0 < w_0 < y && s[x] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1) ||
                                        (exists z_0, w_0 :: y < z_0 < w_0 < z && s[x] == 0 && s[y] == 0 && s[z_0] == 1 && s[w_0] == 1)
                    {
                        if s[z] == 1 {
                            var w := z + 1;
                            while w < |s|
                                invariant z + 1 <= w <= |s|
                                invariant forall w' :: z < w' < w ==> !(s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w'] == 1)
                                invariant res == (exists x_0, y_0, z_0, w_0 :: 0 <= x_0 < y_0 < z_0 < w_0 < x && s[x_0] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1) ||
                                                (exists y_0, z_0, w_0 :: x < y_0 < z_0 < w_0 < y && s[x] == 0 && s[y_0] == 0 && s[z_0] == 1 && s[w_0] == 1) ||
                                                (exists z_0, w_0 :: y < z_0 < w_0 < z && s[x] == 0 && s[y] == 0 && s[z_0] == 1 && s[w_0] == 1) ||
                                                (exists w_0 :: z < w_0 < w && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w_0] == 1)
                            {
                                if s[w] == 1 {
                                    res := true;
                                    return;
                                }
                                w := w + 1;
                            }
                        }
                        z := z + 1;
                    }
                }
                y := y + 1;
            }
        }
        x := x + 1;
    }
    return;
}
// </vc-code>

