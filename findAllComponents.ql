import semmle.code.java.frameworks.android.Android
import semmle.code.xml.AndroidManifest

predicate getPermissionLevel(AndroidManifestXmlFile manifest, string permName, string permLevel) {
  exists(XmlElement permissionElement |
    permissionElement.getFile() = manifest and
    permissionElement.getName() = "permission" and
    permissionElement.getAttributeValue("name") = permName and
    permLevel = permissionElement.getAttributeValue("protectionLevel")
  )
}

from AndroidManifestXmlFile manifest, AndroidComponentXmlElement component, string permNeeded, string permLevel, string exported
where 
  component.getFile() = manifest and
  (
    permNeeded = component.getAttributeValue("permission")
    or
    not exists(component.getAttributeValue("permission")) and permNeeded = "None"
  ) and
  (
    getPermissionLevel(manifest, permNeeded, permLevel)
    or
    (permNeeded.matches("android.permission.%") and permLevel = "System")
    or
    (not permNeeded.matches("android.permission.%") and permNeeded != "None" and permLevel = "Custom")
    or
    permNeeded = "None" and permLevel = "N/A"
  ) and
  (
    exported = component.getAttributeValue("exported")
    or
    not exists(component.getAttributeValue("exported")) and exported = "Not specified"
  )
select
  component.getName() as componentType,
  component.getAttributeValue("name") as componentName,
  exported as isExported,
  permNeeded as permissionNeeded,
  permLevel as permissionLevel
