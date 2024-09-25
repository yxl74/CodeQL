import java
import codeql.xml.Xml
import semmle.code.xml.AndroidManifest

predicate getPermissionLevel(string permName, string permLevel) {
  exists(AndroidManifestXmlFile manifest, XmlElement permElement |
    permElement.getFile() = manifest and
    permElement.getName() = "permission" and
    permElement.getAttributeValue("android:name") = permName and
    permLevel = permElement.getAttributeValue("android:protectionLevel")
  )
}

predicate isAndroidPermission(AndroidPermissionXmlAttribute attr) {
  attr.getValue().matches("android.permission.%")
}

from AndroidManifestXmlFile manifest, AndroidComponentXmlElement component, AndroidPermissionXmlAttribute permAttr, string permLevel
where 
    component.getFile() = manifest and
    component.isExported() and
    permAttr = component.getAnAttribute() and
    (
      if exists(string level | getPermissionLevel(permAttr.getValue(), level))
      then getPermissionLevel(permAttr.getValue(), permLevel)
      else
        if isAndroidPermission(permAttr)
        then permLevel = "system"
        else permLevel = "undefined"
    )
select
    manifest.getAbsolutePath() as filepath,
    component.getName() as type,
    component.getResolvedComponentName() as name,
    permAttr.getValue() as permissionNeeded,
    permLevel as permissionLevel
