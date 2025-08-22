use vstd::prelude::*;

verus!{
	fn myfun(a: &mut Vec<i32>, N: u32)
		// pre-conditions-start
		requires
			N > 0,
			old(a).len() == N,
		// pre-conditions-end
		// post-conditions-start
		ensures
			forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
		// post-conditions-end
	{
		let target_parity = (N % 2) as i32;
		
		for i in 0..N
			invariant
				a.len() == N,
				forall |k:int| 0 <= k < i ==> a[k] % 2 == target_parity,
		{
			/* code modified by LLM (iteration 4): Simplified logic to ensure parity is correctly set */
			let current_value = a[i as usize];
			if current_value % 2 != target_parity {
				// Need to change parity - add or subtract 1 based on overflow safety
				if current_value < i32::MAX {
					a.set(i as usize, current_value + 1);
				} else {
					a.set(i as usize, current_value - 1);
				}
			}
			
			/* code modified by LLM (iteration 4): Fixed type mismatch by using int index */
			assert(a[i as int] % 2 == target_parity);
		}
	}
}

fn main() {}