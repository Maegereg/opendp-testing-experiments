# type: ignore
# analogous to impl MakeNoise<VectorDomain<AtomDomain<IBig>>, MI, MO> for RV in Rust
class RV:
    def make_noise_threshold(
        self,
        input_space: tuple[MapDomain[AtomDomain[TK], AtomDomain[IBig]], MI],
        threshold: IBig,
    ) -> Measurement[
        MapDomain[AtomDomain[TK], AtomDomain[IBig]], HashMap[TK, IBig], MI, MO
    ]:
        input_domain, input_metric = input_space
        output_measure = MO.default()
        threshold_magnitude = threshold.into_parts()[1]  # |\label{line:threshold-mag}|
        privacy_map = self.noise_threshold_privacy_map(  # |\label{line:privacy-map}|
            input_metric, output_measure, threshold_magnitude
        )

        match threshold.sign():
            case Sign.Positive:
                beyond = Ordering.Greater
            case Sign.Negative:
                beyond = Ordering.Less

        def function(data: HashMap[TK, IBig]) -> HashMap[TK, IBig]:
            out = []
            for k, v in data.items():
                # a key with value zero is the same as a missing key
                if v == 0:  # |\label{line:drop-zero}|
                    continue
                v = self.sample(v)  # |\label{line:sample}|

                if v.cmp(threshold) == beyond:
                    out.append((k, v))
            # shuffle the output to avoid leaking the order of the input
            random.shuffle(out)  # |\label{line:shuffle}|
            return dict(out)

        return Measurement.new(
            input_domain,
            Function.new_fallible(function),
            input_metric,
            output_measure,
            privacy_map,
        )
