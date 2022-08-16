procedure return_in_loop() {
    var x: int;

    x := 10;
    while (x > 0)
    {
        if (x == 5)
        {
            assert x == 5;
            return;
        }
        x := x - 1;
    }

    assert x != 5;
}