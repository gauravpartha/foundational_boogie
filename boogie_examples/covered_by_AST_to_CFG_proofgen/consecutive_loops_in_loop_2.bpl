procedure consecutive_loops_in_loop_2() {
    var x: int;
    var y: int;

    havoc y;
    havoc x;

    while (y > 0)
    {
        x := y - 1;
        while (x > 1)
        {
            x := x - 1;
        }

        while (x < 1)
            invariant x <= 1;
        {
            x := x + 1;
        }

        assert x == 1;
        y := y - x;
    }
    assert y == 0;
}