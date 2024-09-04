```
pub fn collect_installed_products(
    product_ini_locations: &HashMap<String, String>,
) -> Result<Vec<Product>, anyhow::Error> {
    log::debug!("Entered collect_installed_products");
    let mut installed_products = Vec::with_capacity(product_ini_locations.len());

    for (product_name, product_ini_location) in product_ini_locations.iter() {
        // If ini file is not found, handle it and continue execution
        let product_result = add_product(product_name, product_ini_location);

        let installed_product = match product_result {
            Ok(product) => product,
            Err(error) => log::debug!("{}", error),
        };
        installed_products.push(installed_product);
    }
    
    Ok(installed_products)
}

Error:
`match` arms have incompatible types
expected `Product`, found `()`rustcClick for full compiler diagnostic
macros.rs(49, 9): Actual error occurred here
macros.rs(61, 34): Error originated from macro call here
macros.rs(160, 23): Error originated from macro call here
main.rs(166, 28): this is found to be of type `sim_message::Product`
main.rs(165, 33): `match` arms have incompatible types
log::macros
macro_rules! debug // matched arm #1
Logs a message at the debug level.
```
