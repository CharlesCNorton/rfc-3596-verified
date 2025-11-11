# RFC 3596: DNS Extensions for IPv6

  **Author:** Charles Norton
  **Date:** November 11, 2025
  **License:** MIT

  Formal verification of RFC 3596 in Coq. Proves AAAA records and IPv6 reverse DNS mapping are mathematically correct.

  ## What's Verified

  - AAAA resource records (§2.1-2.2)
  - IPv6 RDATA codec with bijection proofs
  - Reverse DNS via ip6.arpa (§2.5)
  - Case-insensitive label matching (RFC 1035)
  - Additional-section processing (§3)
  - Dual-stack query strategies (§4)

  ## Results

  ```coq
  Theorem reverse_bijective : forall ip,
    wf_ipv6 ip -> reverse_to_ipv6 (ipv6_to_reverse ip) = Some ip.
  IPv6 ↔ reverse DNS is perfectly invertible.

  Theorem ipv6_bytes_roundtrip_wf : forall ip,
    wf_ipv6 ip -> ipv6_from_bytes (ipv6_to_bytes ip) = Some ip.
  Wire-format serialization is bijective.

  Theorem AAAA_codec_stable : forall bs,
    wf_bytes bs -> encode_AAAA_rdata (decode_AAAA_rdata bs) = bs.
  AAAA RDATA encoding/decoding roundtrips exactly.

  What This Guarantees

  Major DNS servers (BIND, Unbound, PowerDNS) have all shipped IPv6 bugs—buffer overflows, cache poisoning, parsing failures. This eliminates that entire class of errors:

  - No buffer overflows (all bounds proven)
  - No byte-order errors (serialization proven correct)
  - No parsing failures (bijections proven)
  - No integer overflow (modular arithmetic proven)

  OCaml Extraction

  Extraction "dns_ipv6.ml"
    create_aaaa_record
    ipv6_to_reverse
    reverse_to_ipv6
    encode_AAAA_rdata
    decode_AAAA_rdata.

  Generates verified executable code.

  Examples

  AAAA Record

  Definition doc_addr : word128 := (0x20010db8, 0, 0, 1).
  Definition aaaa_rec := create_aaaa_record ["www";"example";"com"] doc_addr 3600.

  Reverse DNS

  Definition loopback : word128 := (0, 0, 0, 1).
  Definition reverse_name := ipv6_to_reverse loopback.
  (* Produces: 1.0.0.0...0.0.0.0.ip6.arpa *)

  Roundtrip Proof

  Example reverse_roundtrip :
    reverse_to_ipv6 (ipv6_to_reverse loopback) = Some (normalize128 loopback).
  Proof. reflexivity. Qed.
```
  Part of Sammath Naur

  This is part of the Sammath Naur project—formal verification of 50+ internet RFCs:

  - 🌬️ Vilya - Network layer
  - 💧 Nenya - DNS infrastructure (this work)
  - 🔥 Narya - Routing protocols
  - 🗻 Ashnazg - Security/cryptography
