-- <vc-preamble>
/-!
{
  "name": "numpy.polynomial.polybase.ABCPolyBase",
  "category": "Polynomial base class",
  "description": "An abstract base class for immutable series classes.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polybase.ABCPolyBase.html",
  "doc": "An abstract base class for immutable series classes.\n\n    ABCPolyBase provides the standard Python numerical methods\n    '+', '-', '*', '//', '%', 'divmod', '**', and '()' along with the\n    methods listed below.\n\n    Parameters\n    ----------\n    coef : array_like\n        Series coefficients in order of increasing degree, i.e.,\n        \`\`(1, 2, 3)\`\` gives \`\`1*P_0(x) + 2*P_1(x) + 3*P_2(x)\`\`, where\n        \`\`P_i\`\` is the basis polynomials of degree \`\`i\`\`.\n    domain : (2,) array_like, optional\n        Domain to use. The interval \`\`[domain[0], domain[1]]\`\` is mapped\n        to the interval \`\`[window[0], window[1]]\`\` by shifting and scaling.\n        The default value is the derived class domain.\n    window : (2,) array_like, optional\n        Window, see domain for its use. The default value is the\n        derived class window.\n    symbol : str, optional\n        Symbol used to represent the independent variable in string\n        representations of the polynomial expression, e.g. for printing.\n        The symbol must be a valid Python identifier. Default value is 'x'.\n\n        .. versionadded:: 1.24\n\n    Attributes\n    ----------\n    coef : (N,) ndarray\n        Series coefficients in order of increasing degree.\n    domain : (2,) ndarray\n        Domain that is mapped to window.\n    window : (2,) ndarray\n        Window that domain is mapped to.\n    symbol : str\n        Symbol representing the independent variable.\n\n    Class Attributes\n    ----------------\n    maxpower : int\n        Maximum power allowed, i.e., the largest number \`\`n\`\` such that\n        \`\`p(x)**n\`\` is allowed. This is to limit runaway polynomial size.\n    domain : (2,) ndarray\n        Default domain of the class.\n    window : (2,) ndarray\n        Default window of the class.",
  "code": "class ABCPolyBase(abc.ABC):\n    \"\"\"An abstract base class for immutable series classes.\n\n    ABCPolyBase provides the standard Python numerical methods\n    '+', '-', '*', '//', '%', 'divmod', '**', and '()' along with the\n    methods listed below.\n\n    Parameters\n    ----------\n    coef : array_like\n        Series coefficients in order of increasing degree, i.e.,\n        \`\`(1, 2, 3)\`\` gives \`\`1*P_0(x) + 2*P_1(x) + 3*P_2(x)\`\`, where\n        \`\`P_i\`\` is the basis polynomials of degree \`\`i\`\`.\n    domain : (2,) array_like, optional\n        Domain to use. The interval \`\`[domain[0], domain[1]]\`\` is mapped\n        to the interval \`\`[window[0], window[1]]\`\` by shifting and scaling.\n        The default value is the derived class domain.\n    window : (2,) array_like, optional\n        Window, see domain for its use. The default value is the\n        derived class window.\n    symbol : str, optional\n        Symbol used to represent the independent variable in string\n        representations of the polynomial expression, e.g. for printing.\n        The symbol must be a valid Python identifier. Default value is 'x'.\n\n        .. versionadded:: 1.24\n\n    Attributes\n    ----------\n    coef : (N,) ndarray\n        Series coefficients in order of increasing degree.\n    domain : (2,) ndarray\n        Domain that is mapped to window.\n    window : (2,) ndarray\n        Window that domain is mapped to.\n    symbol : str\n        Symbol representing the independent variable.\n\n    Class Attributes\n    ----------------\n    maxpower : int\n        Maximum power allowed, i.e., the largest number \`\`n\`\` such that\n        \`\`p(x)**n\`\` is allowed. This is to limit runaway polynomial size.\n    domain : (2,) ndarray\n        Default domain of the class.\n    window : (2,) ndarray\n        Default window of the class.\n\n    \"\"\"",
  "type": "class"
}
-/

-- TODO: Implement ABCPolyBase
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>