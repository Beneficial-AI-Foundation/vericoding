use vstd::prelude::*;

verus!{

    fn main() {
        /* code modified by LLM (iteration 1): removed println! macro as it's not supported in Verus */
        let result = generate_all_combinations(5, 3);
        // println!("Generated {} combinations", result.len()); // Not supported in Verus
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
        let mut current_list = Vec::new();
        
        if k <= 0 || n <= 0 || k > n {
            return total_list;
        }
        
        create_all_state(1, n, k, &mut current_list, &mut total_list);
        total_list
    }

    /* code modified by LLM (iteration 4): added preconditions and guards to prevent arithmetic overflow/underflow */
    fn create_all_state(
        increment: i32,
        total_number: i32,
        level: i32,
        current_list: &mut Vec<i32>,
        total_list: &mut Vec<Vec<i32>>,
    )
        requires 
            increment >= 1,
            total_number >= 1,
            level >= 0,
            level <= total_number,
            increment <= total_number
        decreases level
    {
        if level == 0 {
            total_list.push(myVecClone(current_list));
            return;
        }
        
        /* code modified by LLM (iteration 4): added guard to prevent arithmetic underflow */
        if level > total_number + 1 {
            return;
        }
        
        let mut i = increment;
        /* code modified by LLM (iteration 4): added bounds check and updated loop condition to prevent overflow */
        let upper_bound = total_number - level + 1;
        while i <= upper_bound && i <= total_number
            invariant 
                increment <= i,
                level > 0,
                level <= total_number,
                total_number >= 1,
                i >= 1
            decreases upper_bound - i + 1
        {
            current_list.push(i);
            create_all_state(i + 1, total_number, level - 1, current_list, total_list);
            current_list.pop();
            i += 1;
        }
    }
}