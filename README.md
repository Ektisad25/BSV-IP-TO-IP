# BSV-IP-TO-IP
1-replace with your keys in line 2030-->2034
2- fund your PAYER_SPEND_WIF with some BSV satoshis

```text
                    +----------------------+
                    |      Payer Wallet    |
                    |----------------------|
                    | Identity Key (ID)    |
                    | Anchor Key (ANC)     |
                    | Spend Key (SPEND)    |
                    +----------------------+
                               |
                               | derive_sender_change_address(i)
                               v
                    +----------------------+
                    |  Change Address #i   |
                    | (controlled by SPEND)|
                    +----------------------+
                               |
                               | (used for sending change back to self)
                               |
                               v
    ----------------- Transaction -----------------
    |                                            |
    |  Outputs:                                  |
    |   - Plan #0 Receive Address (Payee)        |
    |   - Plan #1 Receive Address (Payee)        |
    |   - ...                                    |
    |   - Change Address (Payer)                 |
    ------------------------------------------------
                               |
                               | broadcast via BSV network
                               v
                    +----------------------+
                    |   Payee Wallet       |
                    |----------------------|
                    | Identity Key (ID)    |
                    | Anchor Key (ANC)     |
                    +----------------------+
                               |
                               | derive_recv_address(i)
                               v
                    +----------------------+
                    | Receive Address #i   |
                    | (controlled by Payee)|
                    +----------------------+
...
Key points:

The payer uses three keys: Identity, Anchor, Spend. Only the Spend key actually signs the transaction and moves funds.

The payee uses two keys: Identity and Anchor. The payee’s receive addresses are derived from these keys, so the payer doesn’t need the payee’s private keys—only the derived addresses.

Change addresses always belong to the payer. That’s why you don’t need the payee’s keys for change.

Everything happens via the BSV network, not direct IP. The network ensures your transaction reaches the recipient.


my address donation

1ERc7xAG9oDZtw4a9x7oTGYxz6PLzqfM2Z
