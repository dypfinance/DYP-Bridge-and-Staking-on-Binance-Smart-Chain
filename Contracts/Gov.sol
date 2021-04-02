/**
 *Submitted for verification at Etherscan.io on 2021-01-23
*/

// SPDX-License-Identifier: BSD-3-Clause
pragma solidity 0.6.11;

/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {
  function mul(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a * b;
    assert(a == 0 || c / a == b);
    return c;
  }

  function div(uint256 a, uint256 b) internal pure returns (uint256) {
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return c;
  }

  function sub(uint256 a, uint256 b) internal pure returns (uint256) {
    assert(b <= a);
    return a - b;
  }

  function add(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.3._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.3._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

interface Token {
    function approve(address, uint) external returns (bool);
    function balanceOf(address) external view returns (uint);
    function transferFrom(address, address, uint) external returns (bool);
    function transfer(address, uint) external returns (bool);
}

interface LegacyToken {
    function transfer(address, uint) external;
}

interface StakingPool {
    function disburseRewardTokens() external;
    function burnRewardTokens() external;
    function transferOwnership(address) external;
    function transferAnyERC20Token(address, address, uint) external;
    function transferAnyOldERC20Token(address, address, uint) external;
}

/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {
    address private _owner;
    address public pendingOwner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev The Ownable constructor sets the original `owner` of the contract to the sender
     * account.
     */
    constructor () internal {
        _owner = msg.sender;
        emit OwnershipTransferred(address(0), _owner);
    }

    /**
     * @return the address of the owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(isOwner());
        _;
    }
    
    /**
   * @dev Throws if called by any account other than the owner.
   */
    modifier onlyPendingOwner() {
        assert(msg.sender != address(0));
        require(msg.sender == pendingOwner);
        _;
    }

    /**
     * @return true if `msg.sender` is the owner of the contract.
     */
    function isOwner() public view returns (bool) {
        return msg.sender == _owner;
    }

    /**
    * @dev Allows the current owner to transfer control of the contract to a newOwner.
    * @param _newOwner The address to transfer ownership to.
    */
    function transferOwnership(address _newOwner) public onlyOwner {
        require(_newOwner != address(0));
        pendingOwner = _newOwner;
    }
  
    /**
    * @dev Allows the pendingOwner address to finalize the transfer.
    */
    function claimOwnership() onlyPendingOwner public {
        _transferOwnership(pendingOwner);
        pendingOwner = address(0);
    }

    /**
     * @dev Transfers control of the contract to a newOwner.
     * @param newOwner The address to transfer ownership to.
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0));
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}


/**
 * @title Governance
 * @dev Governance smart contract for staking pools
 * Takes in DYP as votes
 * Allows addition and removal of votes during a proposal is open
 * Allows withdrawal of all dyp once the latest voted proposal of a user is closed
 * Has a QUORUM requirement for proposals to be executed
 * CONTRACT VARIABLES must be changed to appropriate values before live deployment
 */
contract Governance is Ownable {
    using SafeMath for uint;
    using Address for address;
    // Contracts are not allowed to deposit, claim or withdraw
    modifier noContractsAllowed() {
        require(!(address(msg.sender).isContract()) && tx.origin == msg.sender, "No Contracts Allowed!");
        _;
    }
    
    // ============== CONTRACT VARIABLES ==============
    
    // voting token contract address
    address public constant TRUSTED_TOKEN_ADDRESS = 0xf666B2DeFCC02874576707B8924854e44135aFDb;
    
    // minimum number of votes required for a result to be valid
    // 1 token = 1 vote
    uint public QUORUM = 1000e18;
    
    uint public constant ADMIN_FEATURES_EXPIRE_AFTER = 2 hours;
    
    // Admin can transfer out Governance Tokens from this contract ADMIN_CAN_CLAIM_AFTER
    // duration since creation
    uint public constant ADMIN_CAN_CLAIM_AFTER = 1 hours;
    
    // minimum number of tokens required to initialize a proposal
    uint public MIN_BALANCE_TO_INIT_PROPOSAL = 100e18;
    
    // duration since proposal creation till users can vote
    uint public constant VOTE_DURATION = 5 minutes;
    
    // duration after voting, since a proposal has passed
    // during which the proposed action may be executed
    uint public constant RESULT_EXECUTION_ALLOWANCE_PERIOD = 5 minutes;
    
    // ============ END CONTRACT VARIABLES ============
    
    uint public immutable contractStartTime;
    
    event PoolCallSucceeded(StakingPool);
    event PoolCallReverted(StakingPool, string);
    event PoolCallReverted(StakingPool, bytes);
    
    enum PoolGroupName {
        WBNB,
        WETH,
        BUSD
    }
    
    enum Action {
        DISBURSE_OR_BURN,
        UPGRADE_GOVERNANCE,
        CHANGE_QUORUM,
        TEXT_PROPOSAL,
        CHANGE_MIN_BALANCE_TO_INIT_PROPOSAL
    }
    
    enum Option {
        ONE, // disburse | yes
        TWO // burn | no
    }
    
    mapping (PoolGroupName => StakingPool[4]) public hardcodedStakingPools;
    
    constructor() public {
        contractStartTime = now;
        
        hardcodedStakingPools[PoolGroupName.WBNB][0] = StakingPool(0x927665b6ba0db498436bB1D33a6F6F812DC29B05);
        hardcodedStakingPools[PoolGroupName.WBNB][1] = StakingPool(0x0b0A544AE6131801522E3aC1FBAc6D311094c94c);
        hardcodedStakingPools[PoolGroupName.WBNB][2] = StakingPool(0x16cAaD63BDFC3Ec4A2850336B28efE17e802b896);
        hardcodedStakingPools[PoolGroupName.WBNB][3] = StakingPool(0x512FF8739d39e55d75d80046921E7dE20c3e9BFf);
        
        hardcodedStakingPools[PoolGroupName.WETH][0] = StakingPool(0xAf1639D868fD2842E9B8eE3bD218e955851bd756);
        hardcodedStakingPools[PoolGroupName.WETH][1] = StakingPool(0x8B0e324EEdE360CaB670a6AD12940736d74f701e);
        hardcodedStakingPools[PoolGroupName.WETH][2] = StakingPool(0x78e2dA2eda6dF49BaE46E3B51528BAF5c106e654);
        hardcodedStakingPools[PoolGroupName.WETH][3] = StakingPool(0x350F3fE979bfad4766298713c83b387C2D2D7a7a);
        
        hardcodedStakingPools[PoolGroupName.BUSD][0] = StakingPool(0x7FcDfeCeE90c6A428FE13fE48641D58807B74873);
        hardcodedStakingPools[PoolGroupName.BUSD][1] = StakingPool(0xF4abc60a08B546fA879508F4261eb4400B55099D);
        hardcodedStakingPools[PoolGroupName.BUSD][2] = StakingPool(0x13F421Aa823f7D90730812a33F8Cac8656E47dfa);
        hardcodedStakingPools[PoolGroupName.BUSD][3] = StakingPool(0x86690BbE7a9683A8bAd4812C2e816fd17bC9715C);
    }
    
    
    
    // proposal id => action
    mapping (uint => Action) public actions;
    
    // proposal id => option one votes
    mapping (uint => uint) public optionOneVotes;
    
    // proposal id => option two votes
    mapping (uint => uint) public optionTwoVotes;
    
    // proposal id => staking pool
    mapping (uint => StakingPool[]) public stakingPools;
    
    // proposal id => newGovernance
    mapping (uint => address) public newGovernances;
    
    // proposal id => unix time for proposal start
    mapping (uint => uint) public proposalStartTime;
    
    // proposal id => bool
    mapping (uint => bool) public isProposalExecuted;
    
    mapping (uint => uint) public newQuorums;
    mapping (uint => uint) public newMinBalances;
    mapping (uint => string) public proposalTexts;
    
    // address user => total deposited DYP
    mapping (address => uint) public totalDepositedTokens;
    
    // address user => uint proposal id => uint vote amounts
    mapping (address => mapping (uint => uint)) public votesForProposalByAddress;
    
    // address user => uint proposal id => Option voted for option
    mapping (address => mapping (uint => Option)) public votedForOption;
    
    // address user => start time for the latest proposal the user voted on
    mapping (address => uint) public lastVotedProposalStartTime;
    
    // uint last proposal id
    // proposal ids start at 1
    uint public lastIndex = 0;
    
    // view function to get proposal details
    function getProposal(uint proposalId) external view returns (
        uint _proposalId, 
        Action _proposalAction,
        uint _optionOneVotes,
        uint _optionTwoVotes,
        StakingPool[] memory _stakingPool,
        address _newGovernance,
        uint _proposalStartTime,
        bool _isProposalExecuted,
        uint _newQuorum,
        string memory _proposalText,
        uint _newMinBalance
        ) {
        _proposalId = proposalId;
        _proposalAction = actions[proposalId];
        _optionOneVotes = optionOneVotes[proposalId];
        _optionTwoVotes = optionTwoVotes[proposalId];
        _stakingPool = stakingPools[proposalId];
        _newGovernance = newGovernances[proposalId];
        _proposalStartTime = proposalStartTime[proposalId];
        _isProposalExecuted = isProposalExecuted[proposalId];
        _newQuorum = newQuorums[proposalId];
        _proposalText = proposalTexts[proposalId];
        _newMinBalance = newMinBalances[proposalId];
    }
    
    function changeQuorum(uint newQuorum) external onlyOwner {
        require(now < contractStartTime.add(ADMIN_FEATURES_EXPIRE_AFTER), "Change quorum feature expired!");
        QUORUM = newQuorum;
    }
    
    function changeMinBalanceToInitProposal(uint newMinBalanceToInitProposal) external onlyOwner {
        require(now < contractStartTime.add(ADMIN_FEATURES_EXPIRE_AFTER), "This admin feature has expired!");
        MIN_BALANCE_TO_INIT_PROPOSAL = newMinBalanceToInitProposal;
    }
    
    // Any DYP holder with a minimum required DYP balance may initiate a proposal
    // with the TEXT_PROPOSAL action for a given staking pool
    function proposeText(string memory text) external noContractsAllowed {
        require(Token(TRUSTED_TOKEN_ADDRESS).balanceOf(msg.sender) >= MIN_BALANCE_TO_INIT_PROPOSAL, "Insufficient Governance Token Balance");
        lastIndex = lastIndex.add(1);
        proposalStartTime[lastIndex] = now;
        actions[lastIndex] = Action.TEXT_PROPOSAL;
        proposalTexts[lastIndex] = text;
    }
    
    // Any DYP holder with a minimum required DYP balance may initiate a proposal
    // with the DISBURSE_OR_BURN action for a given staking pool
    function proposeDisburseOrBurn(PoolGroupName poolGroupName) external noContractsAllowed {
        require(poolGroupName == PoolGroupName.WBNB ||
                poolGroupName == PoolGroupName.WETH ||
                poolGroupName == PoolGroupName.BUSD, "Invalid Pool Group Name!");
        require(Token(TRUSTED_TOKEN_ADDRESS).balanceOf(msg.sender) >= MIN_BALANCE_TO_INIT_PROPOSAL, "Insufficient Governance Token Balance");
        lastIndex = lastIndex.add(1);
        
        stakingPools[lastIndex] = hardcodedStakingPools[poolGroupName];
        
        proposalStartTime[lastIndex] = now;
        actions[lastIndex] = Action.DISBURSE_OR_BURN;
    }
    
    // Admin may initiate a proposal
    // with the UPGRADE_GOVERNANCE action for a given staking pool
    function proposeUpgradeGovernance(PoolGroupName poolGroupName, address newGovernance) external noContractsAllowed onlyOwner {
        require(poolGroupName == PoolGroupName.WBNB ||
                poolGroupName == PoolGroupName.WETH ||
                poolGroupName == PoolGroupName.BUSD, "Invalid Pool Group Name!");
                
        require(Token(TRUSTED_TOKEN_ADDRESS).balanceOf(msg.sender) >= MIN_BALANCE_TO_INIT_PROPOSAL, "Insufficient Governance Token Balance");
        lastIndex = lastIndex.add(1);
        
        stakingPools[lastIndex] = hardcodedStakingPools[poolGroupName];
        
        newGovernances[lastIndex] = newGovernance;
        proposalStartTime[lastIndex] = now;
        actions[lastIndex] = Action.UPGRADE_GOVERNANCE;
    }
    
    // Admin may initiate a proposal
    // with the CHANGE_QUORUM action for the Governance
    function proposeNewQuorum(uint newQuorum) external noContractsAllowed onlyOwner {
        require(Token(TRUSTED_TOKEN_ADDRESS).balanceOf(msg.sender) >= MIN_BALANCE_TO_INIT_PROPOSAL, "Insufficient Governance Token Balance");
        lastIndex = lastIndex.add(1);
        newQuorums[lastIndex] = newQuorum;
        proposalStartTime[lastIndex] = now;
        actions[lastIndex] = Action.CHANGE_QUORUM;
    }
    
    // Admin may initiate a proposal
    // with the CHANGE_MIN_BALANCE_TO_INIT_PROPOSAL action for the Governance
    function proposeNewMinBalanceToInitProposal(uint newMinBalance) external noContractsAllowed onlyOwner {
        require(Token(TRUSTED_TOKEN_ADDRESS).balanceOf(msg.sender) >= MIN_BALANCE_TO_INIT_PROPOSAL, "Insufficient Governance Token Balance");
        lastIndex = lastIndex.add(1);
        newMinBalances[lastIndex] = newMinBalance;
        proposalStartTime[lastIndex] = now;
        actions[lastIndex] = Action.CHANGE_MIN_BALANCE_TO_INIT_PROPOSAL;
    }
    
    // Any DYP holder may add votes for a particular open proposal, 
    // with options YES / NO | DISBURSE / BURN | ONE / TWO
    // with `amount` DYP, each DYP unit corresponds to one vote unit
    
    // If user has already voted for a proposal with an option,
    // user may not add votes with another option, 
    // they will need to add votes for the same option
    function addVotes(uint proposalId, Option option, uint amount) external noContractsAllowed {
        require(amount > 0, "Cannot add 0 votes!");
        require(isProposalOpen(proposalId), "Proposal is closed!");
        
        require(Token(TRUSTED_TOKEN_ADDRESS).transferFrom(msg.sender, address(this), amount), "transferFrom failed!");
        
        // if user is voting for this proposal first time
        if (votesForProposalByAddress[msg.sender][proposalId] == 0) {
            votedForOption[msg.sender][proposalId] = option;
        } else {
            if (votedForOption[msg.sender][proposalId] != option) {
                revert("Cannot vote for both options!");
            }
        }
        
        if (option == Option.ONE) {
            optionOneVotes[proposalId] = optionOneVotes[proposalId].add(amount);
        } else {
            optionTwoVotes[proposalId] = optionTwoVotes[proposalId].add(amount);
        }
        totalDepositedTokens[msg.sender] = totalDepositedTokens[msg.sender].add(amount);
        votesForProposalByAddress[msg.sender][proposalId] = votesForProposalByAddress[msg.sender][proposalId].add(amount);
        
        if (lastVotedProposalStartTime[msg.sender] < proposalStartTime[proposalId]) {
            lastVotedProposalStartTime[msg.sender] = proposalStartTime[proposalId];
        }
    }
    
    // Any voter may remove their votes (DYP) from any proposal they voted for 
    // only when the proposal is open - removing votes refund DYP to user and deduct their votes
    function removeVotes(uint proposalId, uint amount) external noContractsAllowed {
        require(amount > 0, "Cannot remove 0 votes!");
        require(isProposalOpen(proposalId), "Proposal is closed!");
        
        require(amount <= votesForProposalByAddress[msg.sender][proposalId], "Cannot remove more tokens than deposited!");
        
        votesForProposalByAddress[msg.sender][proposalId] = votesForProposalByAddress[msg.sender][proposalId].sub(amount);
        totalDepositedTokens[msg.sender] = totalDepositedTokens[msg.sender].sub(amount);
        
        if (votedForOption[msg.sender][proposalId] == Option.ONE) {
            optionOneVotes[proposalId] = optionOneVotes[proposalId].sub(amount);
        } else {
            optionTwoVotes[proposalId] = optionTwoVotes[proposalId].sub(amount);
        }
        
        require(Token(TRUSTED_TOKEN_ADDRESS).transfer(msg.sender, amount), "transfer failed");
    }

    // After the latest proposal the user voted for, is closed for voting,
    // The user may remove all DYP they added to this contract
    function withdrawAllTokens() external noContractsAllowed {
        require(now > lastVotedProposalStartTime[msg.sender].add(VOTE_DURATION), "Tokens are still in voting!");
        require(Token(TRUSTED_TOKEN_ADDRESS).transfer(msg.sender, totalDepositedTokens[msg.sender]), "transfer failed!");
        totalDepositedTokens[msg.sender] = 0;
    }
    
    // After votes for a proposal are closed, the proposal may be executed by anyone
    // If QUORUM is not reached, transaction must revert
    // If winning option has more votes than losing option, winning action is executed
    // Else losing action is executed
    // Each proposal may be executed only once
    function executeProposal(uint proposalId) external noContractsAllowed {
        require (actions[proposalId] != Action.TEXT_PROPOSAL, "Cannot programmatically execute text proposals");
        require (optionOneVotes[proposalId] != optionTwoVotes[proposalId], "This is a TIE! Cannot execute!");
        require (isProposalExecutible(proposalId), "Proposal Expired!");
        
        isProposalExecuted[proposalId] = true;
    
        Option winningOption;
        uint winningOptionVotes;
        
        if (optionOneVotes[proposalId] > optionTwoVotes[proposalId]) {
            winningOption = Option.ONE;
            winningOptionVotes = optionOneVotes[proposalId];
        } else {
            winningOption = Option.TWO;
            winningOptionVotes = optionTwoVotes[proposalId];
        }
        
        // no action will be taken if winningOptionVotes are less than QUORUM
        if (winningOptionVotes < QUORUM) {
            revert("QUORUM not reached!");
        }
        
        if (actions[proposalId] == Action.DISBURSE_OR_BURN) {
            if (winningOption == Option.ONE) {
                for (uint8 i = 0; i < 4; i++) {
                    StakingPool pool = stakingPools[proposalId][i];
                    try pool.disburseRewardTokens() {
                        emit PoolCallSucceeded(pool);
                    } catch Error(string memory reason) {
                        emit PoolCallReverted(pool, reason);
                    } catch (bytes memory lowLevelData) {
                        emit PoolCallReverted(pool, lowLevelData);
                    }
                }
            } else {
                for (uint8 i = 0; i < 4; i++) {
                    StakingPool pool = stakingPools[proposalId][i];
                    try pool.burnRewardTokens() {
                        emit PoolCallSucceeded(pool);
                    } catch Error(string memory reason) {
                        emit PoolCallReverted(pool, reason);
                    } catch (bytes memory lowLevelData) {
                        emit PoolCallReverted(pool, lowLevelData);
                    }
                }
            }
        } else if (actions[proposalId] == Action.UPGRADE_GOVERNANCE) {
            if (winningOption == Option.ONE) {
                for (uint8 i = 0; i < 4; i++) {
                    StakingPool pool = stakingPools[proposalId][i];
                    try pool.transferOwnership(newGovernances[proposalId]) {
                        emit PoolCallSucceeded(pool);
                    } catch Error(string memory reason) {
                        emit PoolCallReverted(pool, reason);
                    } catch (bytes memory lowLevelData) {
                        emit PoolCallReverted(pool, lowLevelData);
                    }
                }
            }
        } else if (actions[proposalId] == Action.CHANGE_QUORUM) {
            if (winningOption == Option.ONE) {
                QUORUM = newQuorums[proposalId];
            }
        } else if (actions[proposalId] == Action.CHANGE_MIN_BALANCE_TO_INIT_PROPOSAL) {
            if (winningOption == Option.ONE) {
                MIN_BALANCE_TO_INIT_PROPOSAL = newMinBalances[proposalId];
            }
        }
    }
    
    // view function to know whether voting for a particular proposal is open
    function isProposalOpen(uint proposalId) public view returns (bool) {
        if (now < proposalStartTime[proposalId].add(VOTE_DURATION)) {
            return true;
        }
        return false;
    }
    
    // View function to know whether voting for a proposal is closed AND 
    // The proposal is within the RESULT_EXECUTION_ALLOWANCE_PERIOD AND
    // Has not been executed yet
    function isProposalExecutible(uint proposalId) public view returns (bool) {
        if ((!isProposalOpen(proposalId)) && 
            (now < proposalStartTime[proposalId].add(VOTE_DURATION).add(RESULT_EXECUTION_ALLOWANCE_PERIOD)) &&
            !isProposalExecuted[proposalId] &&
            optionOneVotes[proposalId] != optionTwoVotes[proposalId]) {
                return true;
            }
        return false;
    }
    
    // function to allow admin to claim *other* ERC20 tokens sent to this contract (by mistake)
    // Admin cannot transfer out reward tokens from this smart contract
    function transferAnyERC20Token(address tokenAddress, address recipient, uint amount) external onlyOwner {
        require (tokenAddress != TRUSTED_TOKEN_ADDRESS || now > contractStartTime.add(ADMIN_CAN_CLAIM_AFTER), "Cannot Transfer Out main tokens!");
        require (Token(tokenAddress).transfer(recipient, amount), "Transfer failed!");
    }
    
    // function to allow admin to claim *other* ERC20 tokens sent to this contract (by mistake)
    // Admin cannot transfer out reward tokens from this smart contract
    function transferAnyLegacyERC20Token(address tokenAddress, address recipient, uint amount) external onlyOwner {
        require (tokenAddress != TRUSTED_TOKEN_ADDRESS || now > contractStartTime.add(ADMIN_CAN_CLAIM_AFTER), "Cannot Transfer Out main tokens!");
        LegacyToken(tokenAddress).transfer(recipient, amount);
    }
    
    // function to allow admin to claim *other* ERC20 tokens sent to pool contract (by mistake)
    // Admin cannot transfer out reward tokens from this smart contract
    function transferAnyERC20TokenFromPool(address pool, address tokenAddress, address recipient, uint amount) external onlyOwner {
        StakingPool(pool).transferAnyERC20Token(tokenAddress, recipient, amount);
    }
    
    // function to allow admin to claim *other* ERC20 tokens sent to pool contract (by mistake)
    // Admin cannot transfer out reward tokens from this smart contract
    function transferAnyLegacyERC20TokenFromPool(address pool, address tokenAddress, address recipient, uint amount) external onlyOwner {
        StakingPool(pool).transferAnyOldERC20Token(tokenAddress, recipient, amount);
    }
    
}