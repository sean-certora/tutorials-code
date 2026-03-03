
// Partial sum of balances.
//   sumOfBalances[x] = \sum_{i=0}^{x-1} balances[i];
ghost mapping(mathint => mathint) sumOfBalances {
    init_state axiom forall mathint addr. sumOfBalances[addr] == 0;
}

// ghost copy of balanceOf
ghost mapping(address => uint256) ghost_balanceOf {
    init_state axiom forall address addr. ghost_balanceOf[addr] == 0;
}

hook Sload uint256 balance balanceOf[KEY address addr] {
    require ghost_balanceOf[addr] == balance;
}

hook Sstore balanceOf[KEY address addr] uint256 balance (uint256 balance_old) {
    havoc sumOfBalances assuming
      forall mathint x. sumOfBalances@new[x] ==
          sumOfBalances@old[x] + (to_mathint(addr) < x ? balance - balance_old : 0);
    ghost_balanceOf[addr] = balance;
}

