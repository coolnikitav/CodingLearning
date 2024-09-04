I have a file sim_message that has this enum in it:

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct Product {
    pub name: ProductName,
    pub version: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub enum ProductName {
    Commercial,
    CentralDriveEV,
    OffHighway,
    Defense,
    AcromagIntegration,
    TCMSelfTest,
    Addons,
    SupportApps,
    Unknown,
}

I have another file called sim_client. I did "use sim_message::Product" in it. However, when i try writing "ProductName::Commercial", it says "failed to resolve: use of undeclared type filename. Consider importing this enum
use sim_message::ProductName". Is having "use sim_message::Product" not enough?
