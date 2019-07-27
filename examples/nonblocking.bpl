// This action is nonblocking, but the prover cannot show it.
procedure {:left}{:layer 1} GetPositiveInt () returns (x:int)
{
  assume x >= 0;
}
