```
pub fn convert_product_vec_to_string(
    product_vector: &Vec<Product>
) -> String {
    let mut product_string = String::new();
    let mut product_entry = String::new();

    for product in product_vector.iter() {
        product_entry.push_str(product.name.as_string());
        product_entry.push_str(": ");
        product_entry.push_str(product.version.as_str());
        product_string.push_str(product_entry.as_str());
        product_entry.clear();
    }

    return product_string;
}
```
