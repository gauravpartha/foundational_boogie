procedure P(x: int, y: int) returns ()
    requires x > 0;
    ensures x+y >= 0;
{
    assume false;
}

procedure caller() returns ()
{
    assume call forall P(*, *);
}