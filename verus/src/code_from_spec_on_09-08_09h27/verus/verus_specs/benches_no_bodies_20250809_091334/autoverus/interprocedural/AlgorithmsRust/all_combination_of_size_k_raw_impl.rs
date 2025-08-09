use vstd::prelude::*;

verus!{

    fn main() {
    }

    fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
        let mut result = Vec::new();
        for i in 0..v.len() {
            result.push(v[i]);
        }
        result
    }

    pub fn generate_all_combinations(n: i32, k: i32) -> Vec<Vec<i32>> {
        let mut total_list = Vec::new();
        if k <= 0 || n <= 0 || k > n {
            return total_list;
        }
        let mut current_list = Vec::new();
        create_all_state(1, n, k, &mut current_list, &mut total_list);
        total_list
    }

    fn create_all_state(
        increment: i32,
        n: i32,
        remaining: i32,
        current_list: &mut Vec<i32>,
        total_list: &mut Vec<Vec<i32>>,
    )
        /* code modified by LLM (iteration 1): Added decreases clause for recursive function */
        decreases remaining
    {
        if remaining == 0 {
            let cloned = myVecClone(current_list);
            total_list.push(cloned);
            return;
        }
        
        let mut i = increment;
        while i <= n - remaining + 1
            decreases n - i + 1
        {
            current_list.push(i);
            create_all_state(i + 1, n, remaining - 1, current_list, total_list);
            current_list.pop();
            i += 1;
        }
    }
}