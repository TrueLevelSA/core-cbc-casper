fixed_hash::construct_fixed_hash!(
    pub struct Hash(64);
);

impl serde::Serialize for Hash {
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        serializer.serialize_bytes(&self.0)
    }
}
