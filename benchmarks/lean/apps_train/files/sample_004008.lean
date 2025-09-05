Your program will receive an array of complex numbers represented as strings. Your task is to write the  `complexSum` function which have to return the sum as a string.

Complex numbers can be written in the form of `a+bi`, such as `2-3i` where `2` is the real part, `3` is the imaginary part, and `i` is the "imaginary unit". 

When you add two complex numbers, the real and the imaginary part needs to be added separately,so for example `2+3i + 5-i = (2+5)+(3i-i) = 7+2i`

Both the complex and the imaginary part can be 0, so `123`, `-2i` or `i` are also complex numbers.

Complex numbers must be returned in their shortest form, so e.g. `0+1*i` should be just `i`, and `10+0i` should be `10`. This is also how you will get them!

For simplicity, the coefficients will always be integers. If the array is empty, return `0`.

Have fun! :)

def complex_sum (arr : List String) : String := sorry

def complex_str (real imag : Int) : String := sorry

def real_part (s : String) : Int := sorry
def imag_part (s : String) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
