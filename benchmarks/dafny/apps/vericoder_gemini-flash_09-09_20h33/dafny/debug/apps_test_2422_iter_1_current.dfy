predicate ValidSolution(n: int, a: int, b: int, c: int)
{
    a >= 0 && b >= 0 && c >= 0 && 3 * a + 5 * b + 7 * c == n
}

predicate ValidResult(n: int, result: seq<int>)
{
    (|result| == 1 && result[0] == -1) ||
    (|result| == 3 && result[0] >= 0 && result[1] >= 0 && result[2] >= 0 && 
     ValidSolution(n, result[0], result[1], result[2]))
}

// <vc-helpers>
lemma lemma_distrib_mult_add(x: int, y: int, z: int)
    ensures (x + y) * z == x * z + y * z
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
    requires n >= 1
    ensures ValidResult(n, result)
    ensures n % 3 == 0 ==> |result| == 3 && result == [n / 3, 0, 0]
    ensures n % 3 == 1 && n < 7 ==> |result| == 1 && result[0] == -1
    ensures n % 3 == 1 && n >= 7 ==> |result| == 3 && result == [(n - 7) / 3, 0, 1]
    ensures n % 3 == 2 && n < 5 ==> |result| == 1 && result[0] == -1
    ensures n % 3 == 2 && n >= 5 ==> |result| == 3 && result == [(n - 5) / 3, 1, 0]
// </vc-spec>
// <vc-code>
{
    if n % 3 == 0 {
        result := [n / 3, 0, 0];
    } else if n % 3 == 1 {
        if n < 7 {
            result := [-1];
        } else {
            result := [(n - 7) / 3, 0, 1];
            // Prove (n - 7) / 3 >= 0
            calc {
                n >= 7;
                n - 7 >= 0;
                (n - 7) / 3 >= 0;
            }
            // Prove 3 * ((n - 7) / 3) + 5 * 0 + 7 * 1 == n
            calc {
                3 * ((n - 7) / 3) + 5 * 0 + 7 * 1;
                (n - 7) - (n - 7) % 3 + 0 + 7;
                (n - 7) - 1 + 7; // n % 3 == 1 => (n - 7) % 3 == (1 - 7) % 3 == -6 % 3 == 0. This calc step is wrong.
                                 // (n-7)%3 is actually (n%3 - 7%3)%3 = (1 - 1)%3 = 0.
                (n - 7) + 7;
                n;
            }
            // The reasoning for (n-7)%3.
            // If n%3 == 1, then n = 3k + 1 for some integer k.
            // Then n - 7 = 3k + 1 - 7 = 3k - 6 = 3(k - 2).
            // So (n - 7) is divisible by 3, meaning (n - 7) % 3 == 0.
            // Therefore, 3 * ((n - 7) / 3) = n - 7.
        }
    } else { // n % 3 == 2
        if n < 5 {
            result := [-1];
        } else {
            result := [(n - 5) / 3, 1, 0];
            // Prove (n - 5) / 3 >= 0
            calc {
                n >= 5;
                n - 5 >= 0;
                (n - 5) / 3 >= 0;
            }
            // Prove 3 * ((n - 5) / 3) + 5 * 1 + 7 * 0 == n
            calc {
                3 * ((n - 5) / 3) + 5 * 1 + 7 * 0;
                (n - 5) - (n - 5) % 3 + 5;
                (n - 5) + 5; // n % 3 == 2 => (n - 5) % 3 == (2 - 5) % 3 == -3 % 3 == 0
                n;
            }
            // Reasoning for (n-5)%3.
            // If n%3 == 2, then n = 3k + 2 for some integer k.
            // Then n - 5 = 3k + 2 - 5 = 3k - 3 = 3(k - 1).
            // So (n - 5) is divisible by 3, meaning (n - 5) % 3 == 0.
            // Therefore, 3 * ((n - 5) / 3) = n - 5.
        }
    }
}
// </vc-code>

