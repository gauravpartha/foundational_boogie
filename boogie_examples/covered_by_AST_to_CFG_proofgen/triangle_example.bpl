procedure triangle(n: int) returns (t: int)
    requires n >= 0;
    ensures t == n*(n-1) div 2;
{
    var m : int;
    m := 0;
    t := 0;
    while(m < n)
        invariant t == (m*(m-1)) div 2;
        invariant m <= n;
        {
            t := t + m;
            m := m + 1;
        }
}