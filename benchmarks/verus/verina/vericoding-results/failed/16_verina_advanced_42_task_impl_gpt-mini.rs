// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): nat to int ordering */
proof fn lemma_nat_to_int(a: nat, b: nat)
    requires a < b,
    ensures (a as int) < (b as int),
{
    proof {
        assert((a as int) < (b as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn max_profit(prices: Seq<usize>) -> (result: usize)
    ensures
        (result == 0 && prices.len() == 0) ||
        (exists|i: int, j: int| 0 <= i < j < prices.len() && prices[j] >= prices[i] && prices[j] - prices[i] == result) ||
        (forall|i: int, j: int| 0 <= i < j < prices.len() ==> prices[j] < prices[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid spec-indexing in runtime by using runtime indexing prices[i] */
    let n: usize = prices.len();
    if n == 0 {
        let result: usize = 0;
        result
    } else {
        let mut i: usize = 1;
        let mut min_price: usize = prices[0];
        let mut min_idx: usize = 0usize;
        let mut max_profit: usize = 0usize;
        let mut buy: usize = 0usize;
        let mut sell: usize = 0usize;
        let mut eq_found: bool = false;
        let mut eq_buy: usize = 0usize;
        let mut eq_sell: usize = 0usize;

        while i < n
            invariant
                0 <= (i as int) && (i as int) <= (n as int),
                forall|a: int, b: int| 0 <= a < b < (i as int) ==> prices@[(b as nat)] - prices@[(a as nat)] <= max_profit,
                forall|k: int| 0 <= k < (i as int) ==> min_price <= prices@[(k as nat)],
                (max_profit > 0 ==> 0 <= (buy as int) < (sell as int) < (i as int) && prices@[(sell as nat)] - prices@[(buy as nat)] == max_profit),
                (eq_found ==> 0 <= (eq_buy as int) < (eq_sell as int) < (i as int) && prices@[(eq_sell as nat)] == prices@[(eq_buy as nat)]),
            decreases (n - i) as nat
        {
            let p: usize = prices[i];
            if p >= min_price {
                let potential: usize = p - min_price;
                if potential > max_profit {
                    max_profit = potential;
                    buy = min_idx;
                    sell = i;
                } else if potential == max_profit {
                    if potential == 0 {
                        if !eq_found {
                            eq_found = true;
                            eq_buy = min_idx;
                            eq_sell = i;
                        }
                    }
                }
            } else {
                min_price = p;
                min_idx = i;
            }
            i = i + 1;
        }

        let result: usize = max_profit;

        proof {
            if max_profit > 0 {
                assert(exists |ii: int, jj: int|
                    ii == (buy as int) && jj == (sell as int) &&
                    0 <= ii && ii < jj && jj < (n as int) &&
                    prices@[(ii as nat)] <= prices@[(jj as nat)] &&
                    prices@[(jj as nat)] - prices@[(ii as nat)] == result);
            } else {
                if eq_found {
                    assert(exists |ii: int, jj: int|
                        ii == (eq_buy as int) && jj == (eq_sell as int) &&
                        0 <= ii && ii < jj && jj < (n as int) &&
                        prices@[(ii as nat)] <= prices@[(jj as nat)] &&
                        prices@[(jj as nat)] - prices@[(ii as nat)] == result);
                } else {
                    assert(forall |ii: int, jj: int| 0 <= ii < jj < (n as int) ==> prices@[(jj as nat)] < prices@[(ii as nat)]);
                }
            }
        }

        result
    }
}
// </vc-code>

}
fn main() {}