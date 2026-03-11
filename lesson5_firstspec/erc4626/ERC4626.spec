using ERC20Concrete as erc20;

methods {
    function balanceOf(address)               external returns(uint256) envfree;
    function allowance(address,address)       external returns(uint256) envfree;
    function totalSupply()                    external returns(uint256) envfree;
    function totalAssets()                    external returns(uint256) envfree;
    function convertToShares(uint256 assets)  external returns(uint256) envfree;
    function convertToAssets(uint256 shares)  external returns(uint256) envfree;
    function previewDeposit(uint256 assets)   external returns(uint256) envfree;
    function previewMint(uint256 shares)      external returns(uint256) envfree;
    function previewWithdraw(uint256 assets)  external returns(uint256) envfree;
    function previewRedeem(uint256 shares)    external returns(uint256) envfree;

    /* ERC20 methods */
    function erc20.balanceOf(address)         external returns(uint256) envfree;
    function erc20.totalSupply()              external returns(uint256) envfree;
    function erc20.allowance(address,address) external returns(uint256) envfree;
}

ghost mapping(address => mathint) ghost_assetBalanceOf { // mathint is really important so we don't have overflow on addition of values
    init_state axiom forall address addr. ghost_assetBalanceOf[addr] == 0;
}

ghost mathint sumOfAssetBalances {
    init_state axiom sumOfAssetBalances == 0;
}

hook Sstore erc20.balanceOf[KEY address addr] uint256 b1 (uint256 b0) {
    sumOfAssetBalances = sumOfAssetBalances + b1 - b0;
    ghost_assetBalanceOf[addr] = b1; // IMPORTANT: This MUST be here. Not having this here was causing vacuity problems with other rules. Of course this needs to stay in sync!
}

invariant ghostAssetBalanceEqualsAssetBalance()
    forall address a. ghost_assetBalanceOf[a] == erc20.balanceOf[a]
    {
        preserved constructor() {
            require forall address a. erc20.balanceOf[a] == 0;
        }
    }

invariant sumOfAssetBalancesEqualsGhostSum()
    sumOfAssetBalances == (usum address a. ghost_assetBalanceOf[a])
    {
        preserved constructor() {
            require (usum address a. ghost_assetBalanceOf[a]) == 0, "Sum of ghost asset balances should be zero at construction";
        }

        preserved {
            requireInvariant ghostAssetBalanceEqualsAssetBalance();
        }

    }

invariant sumOfAssetBalancesIsTotalAssetSupply()
    sumOfAssetBalances == erc20.totalSupply()
    {
        preserved constructor() {
            require erc20.totalSupply() == 0, "ERC20 totalSupply should be zero at construction";
        }
        preserved {
            requireInvariant ghostAssetBalanceEqualsAssetBalance();
            requireInvariant sumOfAssetBalancesEqualsGhostSum();
        }
    }

invariant sumOfTwoAssetBalancesLessThanEqualTotalAssetSupply2()
    forall address a1. forall address a2. a1 != a2 => erc20.balanceOf[a1] + erc20.balanceOf[a2] <= erc20.totalSupply
    {
        preserved constructor() {
            require erc20.totalSupply() == 0, "ERC20 totalSupply should start at zero";
        }
        preserved {
            requireInvariant sumOfAssetBalancesIsTotalAssetSupply();
            requireInvariant sumOfAssetBalancesEqualsGhostSum();
            requireInvariant ghostAssetBalanceEqualsAssetBalance();
        }
    }


invariant sumOfTwoAssetBalancesLessThanEqualTotalAssetSupply(address a1, address a2)
    a1 != a2 => erc20.balanceOf[a1] + erc20.balanceOf[a2] <= erc20.totalSupply()
    {
        preserved constructor() {
            require erc20.totalSupply() == 0, "ERC20 totalSupply should start at zero";
        }
        preserved {
            requireInvariant sumOfAssetBalancesIsTotalAssetSupply();
            requireInvariant sumOfAssetBalancesEqualsGhostSum();
//            requireInvariant ghostAssetBalanceEqualsAssetBalance();
        }
    }

/*
 * Partial sums for the ERC4626 vault token balances
 */

// Partial sum of balances.
//   sumOfBalances[x] = \sum_{i=0}^{x-1} balances[i];
ghost mapping(mathint => mathint) sumOfBalances {
    init_state axiom forall mathint addr. sumOfBalances[addr] == 0;
}

// ghost copy of balanceOf
ghost mapping(address => uint256) ghost_balanceOf {
    init_state axiom forall address addr. ghost_balanceOf[addr] == 0;
}

hook Sload uint256 b balanceOf[KEY address addr] {
    require(ghost_balanceOf[addr] == b, "Ghost balance and balance must always remain synced");
}

/*
 *   The havoc here is a bit dangerous because this is not proved
 */
hook Sstore balanceOf[KEY address addr] uint256 b_1 (uint256 b_0) {
    havoc sumOfBalances assuming
      forall mathint x. sumOfBalances@new[x] ==
          sumOfBalances@old[x] + (to_mathint(addr) < x ? b_1 - b_0 : 0);
    ghost_balanceOf[addr] = b_1;
}

invariant sumOfBalancesStartsAtZero()
    sumOfBalances[0] == 0;

invariant sumOfBalancesGrowsCorrectly()
    forall address addr. sumOfBalances[to_mathint(addr) + 1] ==
        sumOfBalances[to_mathint(addr)] + ghost_balanceOf[addr];

invariant sumOfBalancesMonotone()
    forall mathint i. forall mathint j. (i <= j) => (sumOfBalances[i] <= sumOfBalances[j])
    {
        preserved {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
        }
    }

/* "Total supply of the vault is the sum of its balances" */
invariant sumOfBalancesEqualsTotalSupply()
    sumOfBalances[2^160] == to_mathint(totalSupply())
    {
        preserved {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
        }
    }

/* An extra rule not asked for */
rule sumOfTwoBalancesCannotExceedTotalSupply(address addr1, address addr2, env e, method f, calldataarg args)
filtered { f -> !f.isView }
{
    safeAssumptions(e);
    f(e, args);
    assert addr1 != addr2 => ghost_balanceOf[addr1] + ghost_balanceOf[addr2] <= totalSupply();
}

/*******************************************************************************************/



/* This makes it impossible for a user to erc20.transferFrom on the ERC4626 contract's behalf */
invariant noAllowanceForContractOnAsset(address addr)
    erc20.allowance(currentContract, addr) == 0 {
        preserved constructor() {
            require erc20.allowance(currentContract, addr) == 0, "asset should have no allowance for currentContract";
        }
        preserved with(env e) {
            require e.msg.sender != currentContract;
        }
    }


/* "sum of shares cannot exceed the vault's total assets" */
invariant totalSupplyLessThanEqualTotalAssets()
    totalSupply() <= totalAssets()
    {
        preserved with (env e) {
            require e.msg.sender != currentContract; /* FIXME: Still need to prove this */
            requireInvariant noAllowanceForContractOnAsset(e.msg.sender);
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
            requireInvariant sumOfBalancesEqualsTotalSupply();
            requireInvariant ghostAssetBalanceEqualsAssetBalance();
            requireInvariant sumOfAssetBalancesEqualsGhostSum();
            requireInvariant sumOfAssetBalancesIsTotalAssetSupply();
        }
    }

/* Redundant */
invariant sumOfBalancesLessThanEqualTotalAssets()
    sumOfBalances[2^160] <= totalAssets()
    {
        preserved with (env e) {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
            requireInvariant sumOfBalancesEqualsTotalSupply();

            require e.msg.sender != currentContract; /* FIXME: Still need to prove this */
            requireInvariant noAllowanceForContractOnAsset(e.msg.sender);
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
            requireInvariant sumOfBalancesEqualsTotalSupply();
            requireInvariant ghostAssetBalanceEqualsAssetBalance();
            requireInvariant sumOfAssetBalancesEqualsGhostSum();
            requireInvariant sumOfAssetBalancesIsTotalAssetSupply();
            requireInvariant totalSupplyLessThanEqualTotalAssets();
        }
    }


/*
 * "No assets deposited means no shares are minted and vice versa"
 *
 * Interpretation:
 *   If there is no positive balance change of assets then there is no positive balance chance of shares, and vice versa
 *   We explicitly exclude donations
 */

rule noDepositsIffNoSharesMinted(method f, env e, calldataarg args)
filtered { f -> !f.isView && f.contract != erc20 } // Must filter out erc20.transfer and erc20.transferFrom i.e. donation to contract
{
    safeAssumptions(e);
    mathint assetsBefore = totalAssets();
    mathint supplyBefore = totalSupply();
    f(e, args);
    mathint assetsAfter = totalAssets();
    mathint supplyAfter = totalSupply();
    assert (assetsBefore >= assetsAfter) <=> (supplyBefore >= supplyAfter);
}

invariant noAssetsImpliesNoShares()
    totalAssets() == 0 => totalSupply() == 0 // this is only one way
    {
        preserved with (env e) {
            safeAssumptions(e);
        }
    }

/* "minting shares is monotonic" for mint case */
rule shareMintingMonotonicity1() {
    env e;
    storage init = lastStorage;

    uint256 shares0;
    uint256 shares1;
    uint256 assets0;
    uint256 assets1;
    address receiver;

    safeAssumptions(e);
    require (shares0 <= shares1);

    assets0 = mint(e, shares0, receiver) at init;
    assets1 = mint(e, shares1, receiver) at init;

    assert assets0 <= assets1;


}

/* "minting shares is monotonic" but for deposit case */
rule shareMintingMonotonicity2() {
    env e;
    storage init = lastStorage;

    uint256 shares0;
    uint256 shares1;
    uint256 assets0;
    uint256 assets1;
    address receiver;

    safeAssumptions(e);
    require (assets0 <= assets1);

    shares0 = deposit(e, assets0, receiver) at init;
    shares1 = deposit(e, assets1, receiver) at init;

    assert shares0 <= shares1;
}

/*
 * "splitting a deposit into two is not favorable for a user"
 */
rule splittingADepositIsNotFavorableToUser() {
    env e;
    storage init = lastStorage;
    uint256 assets;
    uint256 assetsA;
    uint256 assetsB;

    uint256 shares;
    uint256 sharesA;
    uint256 sharesB;
    address receiver;

    safeAssumptions(e);
    require assets == assetsA + assetsB;

    shares = deposit(e, assets, receiver);

    sharesA = deposit(e, assetsA, receiver) at init;
    sharesB = deposit(e, assetsB, receiver);

    assert sharesA + sharesB <= shares;
}


rule revertOnZeroAssetDeposit() {
    env e;
    address receiver;
    deposit@withrevert(e, 0, receiver);
    assert lastReverted, "deposit should revert on zero assets";
}

rule revertOnZeroAssetsRedeemed() {
    env e;
    address receiver;
    address owner;
    redeem@withrevert(e, 0, receiver, owner);
    assert lastReverted, "redeem should revert on zero assets in previewRedeem";
}

rule revertOnDepositWithInsufficientBalance()
{
    env e;
    address receiver;
    require erc20.balanceOf(e.msg.sender) == 0;
    deposit@withrevert(e, 1, receiver);
    assert lastReverted, "should revert when insufficient balance";
}

rule revertOnMintWithInsufficientBalance()
{
    env e;
    address receiver;

    safeAssumptions(e);
    require erc20.balanceOf(e.msg.sender) == 0;
    require totalAssets() == 1000;
    require totalSupply() == 1000;

    mint@withrevert(e, 1000, receiver);
    assert lastReverted, "should revert when insufficient balance";
}

rule depositReverts(method f, env e)
filtered { f -> f.selector == sig:deposit(uint256,address).selector }
{
    uint256 assets;
    uint256 shares;
    address receiver;

    uint32 depositSelector = sig:deposit(uint256,address).selector;
    uint32 mintSelector = sig:mint(uint256,address).selector;

    bool revertWhen = (f.selector == depositSelector &&
                       (assets == 0 ||                                                   // can't deposit zero
                       e.msg.value != 0 ||                                               // can't send any ETH along
                       erc20.balanceOf[e.msg.sender] < assets ||                         // must have enough assets
                       (erc20.allowance[e.msg.sender][currentContract] < assets) ||      // ERC4626 must have enough allowance
                       (to_mathint(assets) * to_mathint(totalSupply()) > max_uint256) || // large quantity of assets will cause overflow in share calc
                       (previewDeposit(assets) == 0)                                     // at least 1 wei shares must be minted
                       ));

    safeAssumptions(e);
    if (f.selector == depositSelector) {
        deposit@withrevert(e, assets,receiver);
    }
    assert revertWhen <=> lastReverted;
}

function safeAssumptions(env e) {
    requireInvariant sumOfBalancesStartsAtZero();
    requireInvariant sumOfBalancesGrowsCorrectly();
    requireInvariant sumOfBalancesMonotone();
    requireInvariant sumOfBalancesEqualsTotalSupply();

    require e.msg.sender != currentContract; /* FIXME: Still need to prove this */
    requireInvariant noAllowanceForContractOnAsset(e.msg.sender);
    requireInvariant sumOfBalancesStartsAtZero();
    requireInvariant sumOfBalancesGrowsCorrectly();
    requireInvariant sumOfBalancesMonotone();
    requireInvariant sumOfBalancesEqualsTotalSupply();
    requireInvariant ghostAssetBalanceEqualsAssetBalance();
    requireInvariant sumOfAssetBalancesEqualsGhostSum();
    requireInvariant sumOfAssetBalancesIsTotalAssetSupply();
    requireInvariant totalSupplyLessThanEqualTotalAssets();
    requireInvariant noAssetsImpliesNoShares();
}

/* Just a fun rule I wrote */
rule assetsCanExistWithZeroTotalSupplyExceptAfterDeposit(method f, env e, calldataarg args)
filtered { f -> !f.isView }
{
    safeAssumptions(e);
    f(e, args);
    assert totalAssets() > 0 && totalSupply() == 0 => f.selector != sig:deposit(uint256,address).selector;
}


