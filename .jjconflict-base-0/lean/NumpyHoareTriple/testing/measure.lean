/-!
{
  "name": "numpy.testing.measure",
  "category": "Testing Utilities",
  "description": "Return elapsed time for executing code in the namespace of the caller",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.measure.html",
  "doc": "Return elapsed time for executing code in the namespace of the caller.\n\nThe supplied code string is compiled with the Python builtin \`\`compile\`\`. The precision of the timing is 10 milli-seconds. If the code will execute fast on this timescale, it can be executed many times to get reasonable timing accuracy.",
  "code": "def measure(code_str, times=1, label=None):\n    \"\"\"\n    Return elapsed time for executing code in the namespace of the caller.\n\n    The supplied code string is compiled with the Python builtin \`\`compile\`\`.\n    The precision of the timing is 10 milli-seconds. If the code will execute\n    fast on this timescale, it can be executed many times to get reasonable\n    timing accuracy.\n\n    Parameters\n    ----------\n    code_str : str\n        The code to be timed.\n    times : int, optional\n        The number of times the code is executed. Default is 1. The code is\n        only compiled once.\n    label : str, optional\n        A label to identify \`code_str\` with. This is passed into \`\`compile\`\`\n        as the second argument (for run-time error messages).\n\n    Returns\n    -------\n    elapsed : float\n        Total elapsed time in seconds for executing \`code_str\` \`times\` times.\n\n    Examples\n    --------\n    >>> times = 10\n    >>> etime = np.testing.measure('for i in range(1000): np.sqrt(i**2)', times=times)\n    >>> print(\"Time for a single execution : \", etime / times, \"s\")  # doctest: +SKIP\n    Time for a single execution :  0.005 s\n\n    \"\"\"\n    frame = sys._getframe(1)\n    locs, globs = frame.f_locals, frame.f_globals\n\n    code = compile(code_str, \"Test name: %s \" % label, 'exec')\n    i = 0\n    elapsed = jiffies()\n    while i < times:\n        i += 1\n        exec(code, globs, locs)\n    elapsed = jiffies() - elapsed\n    return 0.01*elapsed"
}
-/

-- TODO: Implement measure
