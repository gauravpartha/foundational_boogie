procedure m () {
    var i: int;
    var n: int;

    i := 0;
    assume n > 0;
    while (i < n)
        invariant i <= n;
    {
        i := i+1;
    }
    assert i >= n;    
}