procedure consecutive_loops() {
    var x: int;

    havoc x;
    while (x > 0)
    {
        x := x - 1;
    }

    while (x < 0)
        invariant x <= 0;
    {
        x := x + 1;
    }


    assert x == 0;
}