use vstd::prelude::*;

verus!{

	fn main() {
		// Example usage of the combination generator
		let combinations = generate_all_combinations(4, 2);
		// This would generate: [[1,2], [1,3], [1,4], [2,3], [2,4], [3,4]]
	}

	fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
		let mut result = Vec::new();
		let mut i = 0;
		/* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
		while i < v.len()
			decreases v.len() - i
		{
			result.push(v[i]);
			i += 1;
		}
		result
	}

	pub fn generate_all_combinations(n: i32, k: i32) -> Vec<Vec<i32>> 
	{
		let mut total_list = Vec::new();
		let mut current_list = Vec::new();
		
		if k > 0 && n > 0 && k <= n {
			create_all_state(1, n, k, &mut current_list, &mut total_list);
		}
		
		total_list
	}

	/* code modified by LLM (iteration 4): strengthened requires clause to ensure safe arithmetic operations */
	fn create_all_state
	(
		increment: i32,
		total_number: i32,
		level: i32,
		current_list: &mut Vec<i32>,
		total_list: &mut Vec<Vec<i32>>,
	) 
		requires 
			level >= 0,
			total_number >= level,
			increment >= 1,
			increment <= total_number,
			increment < i32::MAX,
			level > 0 ==> level <= i32::MAX
		decreases level
	{
		if level == 0 {
			// Base case: we've selected enough elements, add current combination
			let cloned_list = myVecClone(current_list);
			total_list.push(cloned_list);
			return;
		}
		
		/* code modified by LLM (iteration 3): added bounds check to prevent arithmetic underflow/overflow */
		if level > total_number {
			return;
		}
		
		// Try each possible next number
		let mut i = increment;
		/* code modified by LLM (iteration 3): restructured loop condition to avoid potential underflow */
		let upper_bound = total_number - level + 1;
		while i <= upper_bound
			decreases upper_bound - i + 1
		{
			// Add current number to combination
			current_list.push(i);
			
			/* code modified by LLM (iteration 4): added bounds checks before arithmetic operations */
			if i < i32::MAX && level > 0 {
				// Recursively generate combinations with remaining positions
				create_all_state(i + 1, total_number, level - 1, current_list, total_list);
			}
			
			// Backtrack: remove current number
			current_list.pop();
			
			i += 1;
		}
	}
}